package typesafety;

# major outstanding issues - see Bugs in the POD

# o. return statements themselves! how could i forget. this whole project was both more complex
#    and easier than expected. easier to do individual things but more things to do. in side of
#    a code block (the loop in check()), if there is a prototype for the code block we're
#    currently doing, make sure all return statements return something of that type.
# o. we should propogate expected type up as we recurse, or else make sure that nothing dies
#    for lack of type data when we're just exploring the tree.
#    we're already narrowing down offending code to the statement, but propogating the
#    type information up would narrow it down to the exact place in the expression that
#    type safety was lost. reporting on the top and bottom would be most useful -
#    if a method argument is wrong and it comes from an expression, which arg has the
#    wrong type and at what point in the expression might both be useful. not sure what
#    i'm going to do with this. $expected in solve_type().
# o. functions should be prototyped too - package would obviously default to current package.
# o. types.pm allows method prototypes like sub foo (int $bar, string $baz) - amazing! how? steal!
# o. we should observe *any* unsafe use of scalars we've defined - that means picking raw padsv's out of
#    the blue in the bytecode tree, and warning or dieing. likewise, we should descend through any
#    unknown ops or known ops used on non-type-checked things. should track expected return type, too.
# o. we must descend into any code references we see defined. they should be pushed onto a 
#    queue, sort of like %knownuniverse.
# o. Sub::Parameters integration
# o. ML-style automatic argument type discerning?
# o. we typecheck scalars, but what about arrays? should be able to unflatten an array and have it
#    satisfy the last requirement(s) for a given type. ie, if more than once instance of a given
#    type appears in a row as the last type in an argument list prototype, we can assume that the
#    array will take care of it.
# o. should we clear $scalars between calls to different methods? i think Perl reuses the pad numbers, so yes.
# o. decyphering lists for the padsv on the end still doesn't work. my FooBar $foo :typed = 1; happily runs.
# o. just for fun, we should use ourself (or a copy of ourselve) on ourself. we should examplify the code style
#    we're proposing other people use.
# o. mangle function names using source filters and do method overloading based on those mangled names?

# major resolved issues:

# v/ implementation badly non-optimal - we scan recursively from each point, but we consider
#    each and every point! we could recurse like we do, but cache opcode=>type like types.pm,
#    or possible start to most deeply nested ops and work outwards, but we might miss prototypes etc.
#    move to tracking return values to and from each seq() number?
#    or, if we're fully recursive, we could walk the op tree ourselves, just going sibling to sibling
#    at the top level, recursing into the depths. yeah, i like that. okey, that's what we've done.
# v/ $a->meth() - $methods{$scalars->{targ of $a}->type()}->{'meth'} should exist, period, or we're trying to
#    call an unprototyped method.
# v/ when multiple things are declared on one line, they each still get their own nextstate.
#    this means we need only process them in the same order. each could link to the next.
#    was being silly about this. now the "declare" subs are just stubs and we extract original
#    data from the bytecode tree.
# v/ drop attributes, perhaps, and use proto() for scalars too. prototype proto():
#    declare FooBar => my $a; 
#    didn't drop attributes, but we added declare().
# v/ use ->sibling() rather than ->next() to skip over sub-expressions when parsing B - in SOME places
# v/ declare() needs B parser logic to back it up
# v/ beware looking for nextstate! makes compound instructions impossible!
# v/ inspect methods in all modules, not just root level main
# v/ CHECK { } is too soon - inserting code into the main tree at CHECK time might be the best solution.
#    scalar attributes and proto() are done runtime, so our check routine would have to be triggered
#    from the end?! just before the main loop? hrm. don't know how this is going to work. manual call
#    for now.

use 5.8.0;
use strict;
no strict 'refs';
use warnings;
our $VERSION = '0.02';
use Carp 'confess';

use B qw( ppname SVf_IOK SVf_NOK SVf_POK SVf_IVisUV OPf_KIDS );
use B::Generate;

# debugging

# $SIG{__DIE__} =  $SIG{INT} = sub {
#    # when someone does kill -INT <our pid> from the command line, dump our stack and exit
#    print STDERR shift, map { (caller($_))[0] ? sprintf("%s at line %d\n", (caller($_))[1,2]) : ''; } 0..30;
#    print STDERR join "\n", @_;
#    exit 1;
# };

# use attributes to flag the desired datatypes. then do simple static analisys, using the B backend.

my %knownuniverse; # all known namespaces - our inspection list
my %args;          # use-time arguments
my $debug = 0;     # debug mode flag
my $curcv;         # codevalue to get pad entries from

my $lastline; my $lastfile; my $lastpack;  # set from COP statements as we go 

sub nastily () { " in package $lastpack, file $lastfile, line $lastline"; }

#
# allow user to specify what types ought to be
#

sub import {
  my $caller = caller;
  $args{$_}++ foreach @_;
  $debug = $args{debug};
  push @{$caller.'::ISA'}, 'typesafety'; 
  $knownuniverse{$caller}++; 
  *{$caller.'::proto'} = sub {
     my $method = shift;
     die qq{proto syntax: proto 'foo', returns => 'FooBar', takes => 'FooBar', undef, 'FooBar', 'BazQux', undef, undef, undef;\n}
       unless 'returns' eq shift; 
     my $type = shift;
     my $takes = [];
     if(@_) {
       die unless 'takes' eq shift; 
       $takes = [ @_ ];
     }
     (undef, my $filename, my $line) = caller(0); # XX nasty hardcode
     die "filename" unless $filename; die "line" unless $line;
     define_method($caller, $method, get_type_ob($type, $caller, $filename, $line, undef, $method, 'method', $takes));
     # print 'debug: ', $methods->{$caller}->{$method}->diagnostics(), "\n"; 
  };
  *{$caller.'::declare'} = sub :lvalue { 
    $_[1] 
  };
  return 1;
}

#
# data structures
#

{

  my $methods;       # $methods->{$package}->{$methodname} = typeob
  my $scalars;       # $scalars->{$targ} = typeob

  sub get_type_ob {
    # represents a type itself, including where it was defined.
    # type data associated with a typed scalar - includes verbose information about where the type was defined
    # for good diagnostics in case of error
    package typesafety::typeob;
    sub type     { $_[0]->[0] }  # our primary interest - do the types match?
    sub package  { $_[0]->[1] }  # diagnostic output in case of type match failure
    sub filename { $_[0]->[2] }  # diagnostics
    sub line     { $_[0]->[3] }  # diagnostics
    sub pad      { $_[0]->[4] }  # scalars only 
    sub name     { $_[0]->[5] }  # scalars only 
    sub desc     { $_[0]->[6] }  # scalar or method return?
    sub takes    { $_[0]->[7] }  # in the case of methods, what types (in order) do we take for args?
    sub diagnostics { sprintf "%s %s, type %s, defined in package %s, file %s, line %s", map { $_[0]->[$_] || '?' } (6, 5, 0, 1, 2, 3) }
    bless [@_], __PACKAGE__;
  }
  
  sub lookup_method {
    my $package = shift;
    my $method = shift;
    return exists $methods->{$package} if ! defined $method;
    return $methods->{$package}->{$method} if exists $methods->{$package} and exists $methods->{$package}->{$method};
    return undef;
  }
  
  sub define_method {
    my $package = shift;
    my $method = shift;
    my $typeob = shift;
    $methods->{$package}->{$method} = $typeob;
  }
  
  sub lookup_targ {
    my $targ = shift;
    return $scalars->{$targ} if exists $scalars->{$targ};
    # assume first usage and infer type if possible
    my $name = (($curcv->PADLIST->ARRAY)[0]->ARRAY)[$targ];  # from B::Concise
    return unless $name->can('SvSTASH');
    my $type = $name->SvSTASH->NAME; # perl guts, perl guts, rolly polly perl guts
    $type && $type ne 'main' or return undef; # 'main' is voodoo
    $scalars->{$targ} = get_type_ob($type, $lastpack, $lastfile, $lastline, $targ, $name->sv(), 'scalar - first usage');
    return $scalars->{$targ};
  }
  
  sub nuke_scalars {
    # XXX should just key scalars on CV
    $scalars = {};
  }

  sub summary {
    # give a nice report of what we did
    print "typesafety.pm status report:\n";
    print "----------------------------\n";
    foreach my $typeob (values %$scalars) {
      print $typeob->diagnostics(), "\n";
    }
  }

  sub get_arg_ob {
    # represents a place where a type is expected or used.
    # type data associated with method prototype or an opcode. returned from solve_type(), solve_list_type(), and check_args()
    # include some information for diagnostics about where this type was used.
    # XXX if we propoate the expected type, error messages can be given where they are found rather than
    # trying to return them back in diagnostics - maybe? is everything available? then this could go away
    # in favor of plain old type obs. no. not enough information is available. 
    package typesafety::argob;
    sub typeob      { $_[0]->[0] }
    sub diagnostics { $_[0]->[1] }
    bless [ @_ ], __PACKAGE__;
  }

}

#
# verify that types are what the user specified
#

# this is the heart of this module.
# we grok the bytecode, looking for signiture pattern, and extract information
# from them. when a pattern is found, we update internal information, or
# else test internal information to see if something is "safe".

sub check {

  # check the main area first - it may set things up that are in the scope of methods defined later
  $curcv = B::main_cv();
  walkoptree(B::main_root(), \&solve_type, undef); 

  # each package that has used us, check them as well
  foreach my $package (keys %knownuniverse) {
    # print "knownuniverse: ", $package, "\n" if $debug;
    foreach my $method (grep { defined &{$package.'::'.$_} } keys %{$package.'::'}) {
      summary() if(exists $args{summary}); 
      nuke_scalars(); # blow away our concept of what pads are associated with what types as we switch pads
      next if $method eq 'proto';
      next if $method eq 'declare';
      # print "knownuiverse: method: $method\n";
      my $cv = *{$package.'::'.$method}{CODE};
      $curcv = B::svref_2object($cv);
      B::svref_2object($cv)->ROOT() or die;
      # return statements out of methods are expected to return a certain type
      my $expected = lookup_method($package, $method);
      walkoptree(B::svref_2object($cv)->ROOT(), \&solve_type, $expected);
    }
  }

}

#
# crawl the bytecode tree
#

sub walkoptree {
  # experimental - we don't recurse here, we recurse through solve_type(), except in the case of
  # pmops and anoncodes and such. no, we can't even do those here, or else we'll miss most of them XXX.
  my $op = shift;
  my $sub = shift;
  my @args = @_;
  for(my $kid = $op->first(); $$kid; $kid = $kid->sibling()) {
    $debug and print "debug: -------------- ", $kid->name(), ' ', $kid->seq(), "\n";
    $sub->($kid, @args);
    # XXX the last thing should be "return" or else somehow unreachable (if/elseif/else, each with
    # a return as the last thing), and the return value should be consistent with $expected from
    # check(), above. right now, it would have to be enforced here, which is kind of ugly.
  }
  # if (B::class($op) eq 'PMOP' && $op->pmreplroot() && ${$op->pmreplroot()}) {
  #     # pattern-match operators
  #     walkoptree($op->pmreplroot(), $sub);
  # }
}

#
# deduce type given an opcode
#

sub solve_type {

  # what type does an expression return? 

  # this is called for each opcode at the root level of the program, where it recurses
  # to the depths of that node.
  # when an assignment is found, this is called for each of the right and left sides.
  # when a prototyped method call is found, this is called for each argument to that method call.
  # called and recursively by ourself, and indirectly recursively by ourselves by way of
  # solve_list_type() and check_args(), which we call.

  # failure dies. 
  # success returns typesafety::argob object representing the result and the where 
  # bytetree scanning left off.
  # success is easily won when no particular type is expected.
  # XXX - lvalue functions

  my $self = shift;
  my $expected = shift;

  #
  # simple and recursive
  #

  # null - ops that were optimized away

  if(! $self->can('name') or
     $self->isa('B::NULL') or
     $self->name() eq 'null'
     # confess! confess! confess!
  ) {
    $debug and print "debug: ", __LINE__, ": null type: ppname: ", 
                     $self->can('targ') ? ppname($self->targ()) : 'unknown', "\n";

    if($self->can('targ') and
       $self->flags & OPf_KIDS and
       $self->first() and
       $self->first()->sibling() 
    ) {
       # ! $self->first()->isa('B::NULL') and
       # ! $self->first()->sibling()->isa('B::NULL') 
      return solve_type($self->first()->sibling(), $expected);
    }
    return get_arg_ob(undef, 'very unknown construct');
  }

  # nextstate

  # 2     <;> nextstate(main 494 test.pl:32) v ->3

  if($self->name() eq 'nextstate') {

    # record where we are in the program - we use this information to relate bytecode
    # information with information recorded from attributes at compile time.

    $lastpack = $self->stash()->NAME();
    $lastfile = $self->file();
    $lastline = $self->line();

    $debug and print "debug: ", join ' ', '-' x 20, $lastline, $lastfile, $lastpack, '-' x 20, "\n";

  }

  # const

  if($self->name() eq 'const') {
    # very simple case
    print "debug: const\n" if $debug;
    return get_arg_ob(undef, "constant value: '" . $self->sv()->sv() . "'");
  }

  if($self->name() eq 'padsv') {
    # simple case
    # $debug and print "debug: ", __LINE__, ": padsv\n";
    # this happens when we see non-typesafe scalars, which we tolerate ;)
    lookup_targ($self->targ()) or return
      get_arg_ob(undef, "non-type-checked scalar: '" . lexicalname($self->targ()) . '"');
    return get_arg_ob(lookup_targ($self->targ()), lookup_targ($self->targ())->type() . " typed scalar value");
  }

  # list

  if($self->name() eq 'list') {
    # general case - we have a list type, which is the GCD of all types in the list
    # a whole class of problems, really. an sassign is being done to the lvalue result of a list.
    # that lvalue result could be a type-checked variable used in a substr() or other lvalue
    # built in, or it could be a declaration being assigned to right off, perhaps from a 
    # constructor. 
    # solve_types() should be able to go into a list and figure out which type checked scalar (if any)
    # is the fall through value. in order to do this, we'd have to track what arguments go into and
    # come out of each op, and then when the block ends, remember which op was the last. 
    return solve_list_type($self->first()); 
  }

  # sassign
  # aassign

  if($self->name() eq 'sassign' or
     $self->name() eq 'aassign') {{

    $debug and print 'debug: ', __LINE__, ": considering ", $self->name(), " at line $lastline\n";

    # the left hand side is what is being assigned to. if it isn't type-checked,
    # then type checking isn't in effect on this statement.
    # this refers to the side of the assign operator being applied to us.

    # in case of aassign (array assign, one list is assigned to another):
    # instead of calling solve_list_type() as might make sense, we instead just call
    # solve_type(), as either of the lists may have been optimized away, and solve_type()
    # handles this general case, kicking over to solve_list_type() as needed.

    my $leftob = solve_type($self->last(), $expected); my $left = $leftob->typeob(); 

    $debug and print "debug: left type: ", $left ? $left->type() : 'unknown', ' ',
                     'diagnostics: ', $leftob->diagnostics(), 
                     ' opname: ', $self->last()->name(), ' ',
                     " at line $lastline.\n";

    my $rightob = solve_type($self->first(), $expected); my $right = $rightob->typeob();

    $debug and print "debug: right type: ", $right ? $right->type() : 'unknown', ' ',
                     'diagnostics: ', $rightob->diagnostics(), 
                     ' opname: ', $self->first()->name(), ' ',
                     " at line $lastline.\n";

    return $rightob if ! $left;

    $rightob->typeob() or die 'unsafe assignment: ' . $left->diagnostics() . 
                              ' cannot hold ' . $rightob->diagnostics() . ' ' . nastily;

    # do type match exactly? 
    return $left if $right->type() eq $left->type();

    # is the thing on the right a subtype of the variable meant to hold it?
    # this uses softrefs to call ->isa() on a string. the string represents the type.
    return $left if $right->type()->isa($left->type());

    # can't prove it to be safe. sorry.

    die 'unsafe assignment: ' . $left->diagnostics() . ' cannot hold ' .  $right->diagnostics() . ' ' . nastily;

  }}

  #
  # return: a unique case
  #

  # return 1, 2, 3, 4;

  # 8     <@> return K ->9
  # 3        <0> pushmark s ->4
  # 4        <$> const(IV 1) s ->5
  # 5        <$> const(IV 2) s ->6
  # 6        <$> const(IV 3) s ->7
  # 7        <$> const(IV 4) s ->8

  if($self->name() eq 'return') {
    # the pushmark seems to always be there - even on an empty return. 
    # individual items in the list vary, of course.
    my $return = solve_list_type($self->first()->sibling());
    return $return unless $expected;
    die "returning from method, " . $expected->diagnostics() . ' expected, instead, we get a lousy ' .
        $return->diagnostics() if ! $return->type() or ! $return->type()->isa($expected->type());
  }

  #
  # real code and constructs
  #

  # bar->new();

  # b     <2> sassign vKS/2 ->c                     <--- or other stuff
  # 9        <1> entersub[t2] sKS/TARG ->a          <--- this is the node passed to us in this case
  # 3           <0> pushmark s ->4
  # 4           <$> const(PV "bar") sM/BARE ->5
  # 5           <$> const(IV 1) sM ->6
  # 6           <$> const(IV 2) sM ->7
  # 7           <$> const(IV 3) sM ->8
  # 8           <$> method_named(PVIV "new") s ->9
  # a        <0> padsv[$a:3,5] sRM*/LVINTRO ->b

  if($self->name() eq 'entersub') {

     # is it a constructor call? those are self-typing. abstract factories shouldn't use
     # constructors for their dirty work.

     # print "debug: entersub (constructor?), line $lastline\n" if $debug;

     my $op = $self->first();
     my $type;
     my $success = 0;
     my $argop;

     foreach my $test (
       sub { $op->name() eq 'pushmark' },
       sub { return unless $op->name() eq 'const'; $type = $op->sv()->sv(); return 1; },
       sub {
         $argop = $op;
         while($op and $op->name() ne 'method_named') {
           # seek past method call arguments but remember the opcode of the first argument.
           $op = $op->sibling();
         }
         return unless $op; 
         return unless $op->sv()->sv() eq 'new'; 
         $success = 1;
         # print "debug: success\n";
       },
     ) {
       # print "debug: considering: ", $op->name(), "\n";
       last unless $test->(); 
       $op = $op->sibling() or last;
     }

     return check_args($argop, $type, 'new') if $success;

  }

  # $a->bar();

  # this one is tricky. we have to get $a's type to get bar's package to see if that matches $b's type.

  # k        <1> entersub[t4] sKS/TARG ->l       <--- this node is the one given to us
  # c           <0> pushmark s ->d
  # d           <0> padsv[$a:3,5] sM ->e         .... may not be a padsv - should use solve_type()!
  # e           <$> const(IV 5) sM ->f           <--- from here until we hit the method_named op,
  # f           <$> const(IV 4) sM ->g                we these are processed by check_args() for type safety. 
  # g           <$> const(IV 3) sM ->h                the first argument gets held by $argop.
  # h           <$> const(IV 2) sM ->i
  # i           <$> const(IV 1) sM ->j
  # j           <$> method_named(PVIV "bar") s ->k

  if($self->name() eq 'entersub') {

     # print "debug: entersub (method call on typed object)\n" if $debug;

     my $op = $self->first();
     my $method;   # bar, in "$a->bar()"
     my $targ;     # $a, in "$a->bar()", gets us this from its typeob
     my $success = 0;
     my $argop;    # pointer to opcode representing first argument

     foreach my $test (
       sub { $op->name() eq 'pushmark' },
       sub { return unless $op->name() eq 'padsv'; $targ = $op->targ(); return 1; }, 
           # XXX - instead of just a targ holding the object ref, this could be an expression! XXX recurse
       sub { 
         $argop = $op;
         while($op and $op->name() ne 'method_named') {
           $op = $op->sibling();
         }
         return unless $op and $op->name() eq 'method_named'; 
         $method = $op->sv()->sv();                               # bar, in "$b = $a->bar()"
         $success = 1;
       },
     ) {
       # print "debug: ", __LINE__, ": considering: ", $op->name(), "\n";
       last unless $test->(); 
       $op = $op->sibling() or last;
     }

     if($success) {

       if(! lookup_targ($targ)) {
          confess 'missing type information for ' . lexicalname($targ) . 
                  " in expression that should return $expected " . nastily if $expected;
       } else {
         my $type = lookup_targ($targ)->type() or die nastily;          # $a, from "$b = $a->bar()"
         lookup_method($type) or die 'unknown package: ' . $type . ' ' . nastily;
         return check_args($argop, $type, $method);
       }

     }

  }

  #
  # nothing we recognize. we're going to return "unknown", but first we should make sure
  # that expressions nested under this point get inspected for type safety. so, we 
  # recurse, expecting nothing.
  # 

  if($self->flags() & OPf_KIDS) {
    # this should work for unops, binops, *and* listops
    for(my $kid = $self->first(); $$kid; $kid = $kid->sibling()) {
      solve_type($kid, $expected);
    }
  }

  return get_arg_ob(undef, 'unrecognized construct');

}

sub check_args {

  # someone somewhere found something that looks like a method call.
  # we check the arguments to that method call against the methods prototype.
  # we also make sure that that method has a prototype, is a constructor, or else the
  # method appears in the package via can(), since we don't want to compute inheritance manually.
  # XXX if we can track down the package where it is defined, we might find a prototype there
  # we die if the prototype doesn't match the actual types of the chain of ops.
  # in case of a match, we return the argob representing the prototype of this function.

  my $op = shift;
  my $type = shift;
  my $method = shift;

  # no $op means no arguments were found. this might be what the prototype is looking for! is this safe? XXX

  # $debug && ! $op and print "debug: ", __LINE__, " check_args called without an OP! type: $type method: $method\n";
  # $debug && $op and print "debug: ", __LINE__, ": check_args called: op: ", $op->name(), ' ', $op->seq(), 
  #                         " type: $type method: $method\n";

  my $argob;

  # default case - method is prototyped in the package specified by type
  $argob = get_arg_ob(lookup_method($type, $method), 'okey') if lookup_method($type, $method);

  # if method is 'new' and no type exists, default to the type of the reference
  if($method eq 'new' and ! $argob) {
    $argob = get_arg_ob(get_type_ob($type, $type, 'unknown', 0, undef, 'new', 'constructor method'), 'okey') 
  }

  # kludge, but inheritance doesn't work otherwise!
  if(! $argob and $type->can($method)) {
    $argob = get_arg_ob(get_type_ob($type, $type, 'unknown', 0, undef, $method, 'inherited/unprototyped method'), 'okey') 
  }

  $argob or die "unknown method. methods called on type safe objects " .
                 "must be prototyped with proto(). package: " . $type . ' method: ' . $method . ' ' . nastily;

  # at this point, we know the return type of the method call. now, we check the argument signiture, if there is one.
  # if we cooked up our own because new() wasn't prototyped, then there won't be one. that's okey.

  my $takes = $argob->typeob()->takes();

  unless($takes and @$takes) {
    # this method's arguments aren't prototyped
    # success, so far. this is this being assigned to something else, that might conflict.
    # $debug and print "debug: ", __LINE__, ": no 'takes' information found for the type '$type'\n";
    return $argob; 
  }

  # method call arguments get checked for types too! woot!
  # given a list of parameter types and a pointer to an op in a bytecode stream, return undef
  # for success or an error message if there is a type mismatch between the two.

  if(!$argob and scalar(@$takes)) {
    die "arguments were expected, but none were provided, calling $method in $type, " . nastily;
  }

  my $index = 0;
  my $leftop = $op; my $left;
  my $rightargob; my $righttypeob;

  while($leftop and $leftop->name() ne 'method_named') {

    if(! exists $takes->[$index]) {
      die "more parameters passed than specified in prototype. calling $method in $type, " . nastily;
    }

    # $debug and print "debug: ", __LINE__, ": checking prototype: considering: ", $leftop->name(), "\n";

    $left = $takes->[$index];
    goto OKEY if ! $left;

    $rightargob = solve_type($leftop, $left); $righttypeob = $rightargob->typeob();

    if($left and ! $righttypeob) {
      die "argument number " . ($index + 1) . " must be type $left according to prototype. " . 
           'instead, it is a(n) ' . $rightargob->diagnostics() . nastily;
    }

    # righttypeob->isa(left)
    goto OKEY if $righttypeob->type() eq $left;
    goto OKEY if $righttypeob->type()->isa($left);
    die "argument number " . ($index + 1) . " type mismatch: must be type '$left', instead we got a(n) " .
        $righttypeob->type() . ' ' . nastily; 

    OKEY:
    $leftop = $leftop->sibling() or last;
    $index++;

  }

  if($index < @$takes) {
    die "insufficient number of paramenters - only got " . ($index + 1) . ", expecting " . ((scalar @$takes) + 1) . ' .' .
        nastily;
  }

  return $argob; # success

}

#
# stolen from types.pm by Auther Bergman, then hacked into worthlessness
#

# part of the effort to merge types.pm and typesafety.pm

sub solve_list_type {

    # a 'list' op was found - any number of things could be littered onto the stack.
    # this calculates the largest common type of those objects, if any. yes, this means
    # arrays can't contain mixed information - they're an array of one kind of object
    # or integers or floats or something. 
    # the first sibling under list is passed in.
    # this is called from solve_type(), and itself calls solve_type().
    # was get_list_proto().

    my $op = shift;

    my @types;

    # return get_arg_ob(undef, "not yet implemented");

    while(ref($op) ne 'B::NULL') {
        push @types, solve_type($op, undef);
        $op = $op->sibling();
    }

    # which object, if any, encapsulates all of the others?
    # if there are several, they must all be the same class, right?
    # if there are none, there is no common type to this list!

    my @encapsulates;

    OUTTER: 
    foreach my $outter (@types) {
     
      foreach my $inner (@types) {
        next unless $inner->typeob();
        next OUTTER unless $outter->typeob();
        next OUTTER unless $outter->typeob() eq $inner->typeob() or $outter->typeob()->isa($inner->typeob());
      }
      push @encapsulates, $outter;
    }

    $debug and print "debug: ", __LINE__, ": aren't we clever? we think we know the greatest common type, ",
                     "and that is: ", @encapsulates && $encapsulates[0]->typeob() ? $encapsulates[0]->typeob()->type() : ' NONE', "! so there ya have it, folks.\n";

    return get_arg_ob(undef, "no common type in list") if ! @encapsulates;
    return get_arg_ob($encapsulates[0], "list common type"); # XXX this ain't right. okey, why not? 
    
}

#
# utility methods
#

# these just factor out some of the cruftier syntax

sub lexicalname {
  # given a pad number (stored in all perl operators as $op->targ()), return its name.
  # works well - we get "$foo" etc back
  # PVX() returns the string stored in a scalar as null terminated, ignoring the length info, 
  # which is the correct thing to do with pad entries (length info is barrowed for something else).
  my $targ = shift;
  my $padname = (($curcv->PADLIST->ARRAY)[0]->ARRAY)[$targ];  # from B::Concise

  # print "debug: ", $padname->SvSTASH->NAME, "\n"; # XXX - avoid requirement for :typed if we want!
  # print "debug: ", $padname->PV, "\n";

  return 'SPECIAL' if B::class($padname) eq 'SPECIAL';
  return $padname->PVX(); 
}

sub lexicalref {
  # given a pad number, return a B object representing it as a scalar.
  # pads are stored as a parallel array of names/metainformation and actual scalar references to the data.
  my $targ = shift;
  (($curcv->PADLIST->ARRAY)[1]->ARRAY)[$targ]->sv(); 
}

1;

=pod

=head1 NAME

typesafety.pm - compile-time type usage static analysis 

=head1 SYNOPSIS

  package main;
  use typesafety;

  # use typesafety 'summary';

  my FooBar $foo;        # establish type-checked variables
  my FooBar $bar;        # FooBar is the base class of references $bar will hold
  my BazQux $baz;

  $foo = new FooBar;     # this is okey, because $foo holds FooBars
  $bar = $foo;           # this is okey, because $bar also holds FooBars
  # $foo = 10;           # this would throw an error - 10 is not a FooBar
  # $baz = $foo;         # not allowed - FooBar isn't a BazQux
  $foo = $baz;           # is allowed -  BazQux is a FooBar because of inheritance
  $bar = $foo->foo();    # this is okey, as FooBar::foo() returns FooBars also

  typesafety::check();   # perform type check static analysis

  #

  package FooBar;
  use typesafety;

  # unneeded - new() defaults to prototype to return same type as package
  # proto 'new', returns => 'FooBar'; 

  proto 'foo', returns => 'FooBar'; 

  # proto 'methodname', returns => 'FooBar', takes => 'Type', 'Type', 'Type';


  sub new {
    my $type = shift; $type = ref $type if ref $type;
    bless [], $type;
  }

  sub foo { my $me = shift; return $me->new(); } 

  #

  package BazQux;
  use typesafety;
  @ISA = 'FooBar';

=head1 DESCRIPTION

Prevents you from mistakenly bathing cats.

Scenarios:

=over 2

=item Somewhere between point A and point B, a value stops being what you expect.
      You start inserting locks of checks to figure out where the value went
      wrong.

=item Sometimes a return value is what you want, but sometimes other things come back,
      so you have to continiously add checks in the code.

=item All objects are basically the same. Things that want an object will take any
      object and try to deal with it, often by just throwing errors if a given
      method doesn't exist (C<< ->can() >> returns false). This leads to large
      numbers of checks, yet no number of checks make you feel confident that you've
      covered everything that can go wrong.

=item You're limited in how large of programs you can write, because you can't
      keep everything straight after a while. And you're tired of writing
      checks.

=back

  This is a SNAPSHOT release of ALPHA software. This is the second snapshot.
  The first was ugly, ugly, ugly and contained horrific bugs and the implementation
  was lacking. Much remains to be done and much is in progress, but I can't
  stand the thought of anyone looking at the original code. Return types
  still need to be checked. The first one went out the door with a bug
  that kept method parameters from being checked - this is fixed. There are
  tests, but they aren't automated yet. It always just succeds if it compiles.
  The interface has changed and this documentation is wrong - variables
  should no longer be declared with the :typed attribute attached to them,
  and the alternate syntax is no longer supported. Early support for 
  lists are in - lists are considered to be of the type of the common
  type of all elements.

Failure to keep track what kind of data is in a given variable or returned 
from a given method is an epic source of confusion and frustration during
debugging. 

Given a C<< ->get_pet() >> method, you might try to bathe the output. If it always
a dog during testing, everything is fine, but sooner or later, you're
going to get a cat, and that can be rather bloody.

Welcome to Type Safety. Type Safety means knowing what kind of data you
have (atleast in general - it may be a subclass of the type you know
you have). Because you always know what kind of data it is, you see in
advance when you try to use something too generic (like a pet) where you
want something more specific (like a dog, or atleast a pet that implements
the "washable" interface).

Think of Type Safety as a new kind of variable scoping -
instead of scoping where the variables can be seen from, you're scoping
what kind of data they might contain.

"Before hand" means when the program is parsed, not while it is running.
This prevents bugs from "hiding". I'm sure you're familiar with
evil bugs, lurking in the dark, il-used corners of the program, like
so many a grue.
Like Perl's C<use strict> and C<use warnings> and C<use diagnostics>,
potential problems are brought to your attention before they are
proven to be a problem by tripping on them while the program happens
on that nasty part of code.  You might get too much information, but you'll
never have to test every aspect of the program to try to uncover
these sorts of warnings. Now you understand the difference between
"run time diagnostics" and "compile time warnings".

Asserts in the code, checking return values manually, are an example of
run-time type checking:

  # we die unexpectedly, but atleast bad values don't creep around!
  # too bad our program is so ugly, full of checks and possible bad
  # cases to check for...

  my $foo = PetStore->get_pet();
  $foo->isa('Dog') or die; 

Run-time type checking misses errors unless a certain path of execution
is taken, leaving little time bombs to go off, showing up later. More
importantly, it clutters up the code with endless "debugging" checks,
known as "asserts", from the C language macro of the same name.

Type Safety is a cornerstone of Object Oriented programming. It works
with Polymorphism and Inheritance (including Interface Inheritance).

Use C<typesafety.pm> while developing. Comment out the C<typesafety::check()> statement when
placing the code into production. This emulates what is done with compiled
languages - types are checked only after the last time changes are made
to the code. The type checking is costly in terms of CPU, and as long as the
code stays the same, the results won't change. If everything was type
safe the last time you tested, and you haven't changed anything, then it
still is.

A very few, very specific things are inspected in the program when 
C<typesafety::check()> is called:

  $a = $b;

Variable assignment.
Rules are only applied to variables that are "type safe" - a type safe
variable was declared using one of the two constructs shown in the
L<SYNOPSIS>. If it isn't type safe, none of these rules apply.
Otherwise, 
C<$b> must be the same type as C<$a>, or a subclass of C<$a>'s type.
In other words, the types must "match".

  $a->meth();

Method call. If C<$a> is type safe, then the method C<meth()> must
exist in whichever package C<$a> was prototyped to hold a 
reference to. Note that type safety can't keep you from trying
to use a null reference (uninitialized variable), only from trying
to call methods that haven't been proven to be part of the
module they're prototyped to hold a reference to. If the method
hasn't been prototyped in that module, then a C<< ->can() >>
test is done at compile time. Inheritance is handled this way.

  $a = new Foo;

Package constructors are always assumed to return an object of the same type
as their package. In this case, C<< $a->isa('Foo') >> is expected to be
true after this assignment. This may be overridden with a prototype for your
abstract factory constructors (which really belong in another method anyway,
but I'm feeling generous). The return type of C<< Foo->new() >> must match
the type of C<$a>, as a seperate matter. To match, it must match exactly or 
else be a subclass of C<$a> expects. This is just like the simple case
of "variable assignment", above.
If C<new()> has arguments prototyped for it, the
arguments types must also match. This is just like "Method call", above.

  $a = $foo->new();

Same as above. If C<$foo> is type checked and C<$a> is not, then arguments
to the C<new()> method are still checked against any prototype.
If C<$a> is type checked, then the return value of C<new()> must match.
If no prototype exists for C<new()> in whatever package C<$foo> belongs
to, then, as above, the return value is assumed to be the same as the
package C<$foo> belongs to. In other words, in normal circumstances,
you don't have to prototype methods.

  $b = $a->bar();

As above: the return type of C<bar()> must be the same as, or a subclass
of, C<$b>'s, if C<$b> is type safe. If C<$a> is type safe and there is
a prototype on C<bar()>, then argument types are inforced.

  $b = $a->bar($a->baz(), $z->qux());

The above rules apply recursively: if a method call is made to compute
an argument, and the arguments of the C<bar()> method are prototyped,
then the return values of method calls made to compute the arguments
must match the prototype. Any of the arguments in the prototype may be 
C<undef>, in which case no particular type is enforced. Only 
object types are enforced - if you want to pass an array reference,
then bless that array reference into a package and make it an object.

  typesafety::check(); 

This must be done after setting things up to perform actual type checking, or
it can be commented out for production. The module will still need to be used
to provide the C<proto()>, and add the C<attribute.pm> interface handlers.

Giving the 'summary' argument to the C<use typesafety> line generates a report
of defined types when C<typesafety::check()> is run:

  typesafety.pm status report:
  ----------------------------
  variable $baz, type BazQux, defined in package main, file test.7.pl, line 36
  variable $bar, type FooBar, defined in package main, file test.7.pl, line 34
  variable $foo, type FooBar, defined in package main, file test.7.pl, line 33

I don't know what this is good for except warm fuzzy feelings.

You can also specify a 'debug' flag, but I don't expect it will be very helpful
to you.

=head1 OTHER MODULES

L<Class::Contract> by Damian Conway. Let me know if you notice any others.
Class::Contract only examines type safety on arguments to and from method
calls. It doesn't delve into the inner workings of a method to make sure
that types are handled correctly in there. This module covers the same
turf, but with less syntax and less bells and whistles. This module
is more natural to use, in my opinion.

To the best of my knowledge, no other module attempts to do what this
modules, er, attempts to do.

L<Object::PerlDesignPatterns> by myself. Documentation.
Deals with many concepts surrounding
Object Oriented theory, good design, and hotrodding Perl. The current
working version is always at L<http://perldesignpatterns.com>. 

=head1 DIAGNOSTICS

  unsafe assignment:  in package main, file test.7.pl, line 42 - variable $baz, 
  type BazQux, defined in package main, file test.7.pl, line 36 cannot hold method 
  foo, type FooBar, defined in package FooBar, file test.7.pl, line 6 at 
  typesafety.pm line 303.

There are actually a lot of different diagnostic messages, but they are all
somewhat similar. Either something was being assigned to something it shouldn't
have been, or else something is being passed in place of something it shouldn't
be. The location of the relavent definitions as well the actual error are
included, along with the line in C<typesafety.pm>, which is only useful to me.

=head1 BUGS

My favorite section!

Yes, every module I write mentions Damian Conway =)

This module uses the experimental C<attributes.pm> module. As such, this module is
also experimental (as if it doesn't have enough problems already). It may break
in future versions of Perl. Also, we're intimately tied to the bytecode tree,
the structure of which could easily change in future versions of Perl. This
works on my 5.9.0 pre-alpha. It might not work at all on what you have.

Only operations on lexical C<my> variables are supported. Attempting to
assign a global to a typed variable will be ignored - type errors
won't be reported. Global variables themselves cannot be type checked.
Again, all doable, just ran out of steam.

Only operations on methods using the C<< $ob->method(args) >> syntax is 
supported - function calls are not prototyped nor recognized. Stick
to method calls for now.

Types should be considered to match if the last part matches - C<< Foo::Bar->isa('Bar') >> would be true.
This might take some doing. Workaround to C<::> not being allowed in attribute-prototypes.
Presently, programs with nested classes, like C<Foo::Bar>, cannot have these types assigned
to variables. No longer true - the C<declare()> syntax is a work-around to this.

Can't solve complex expressions in arguments to methods or on the right of assignments. 
Anything more complex than a method call stumps the thing. In theory, every construct
could be supported, but that would take a lot of code to do. Java essentially does this -
the compiler knows how to grok the argument and return types of every operator, 
expression, construct, library method, and user code method. We have to simply ignore
things we don't understand.

We use B::Generate just for the C<< ->sv() >> method. Nothing else. I promise! We're not modifying
the byte code tree, just reporting on it. I B<do> have some ideas for using B::Generate,
but don't go off thinking that this module does radical run time self modifying code stuff.

Todo: Integration with interface.pm (don't allow method calls unless that sub is there)
and with L<Class::Lexical> (typed lexical-based classes).

The root (code not in functions) of C<main::> is checked, but not the roots of other modules.
I don't know how to get a handle on them. Sorry. Methods and functions in C<main::> and other
namespaces that C<use typesafety;> get checked, of course.

Having to call a "check" function is kind of a kludge but I haven't thought of a better way.
Modules we use have a chance to run at the root level, which lets the C<proto()> functions
all run, if we are used after they are, but the main package has no such benefit. Running
at CHECK time doesn't let anything run. 

The B tree matching, navigation, and type solving logic should be presented as a 
reusable API, and a module specific to this task should use that module. After I 
learn what the pattern is and fascilities are really needed, I'll consider this. 

Argh! Perl fails to link to B::Generate's .so when doing a "make test", so testing
is impossible. Sorry. You get one test, and it is a null test.

Some things just plain might not work as described. Let me know.

=head1 SEE ALSO

L<http://perldesignpatterns.com/?TypeSafety> - look for updated documentation
on this module here - this doc is kind of sparse.

L<types>, by Arthur Bergman - C style type checking on strings, integers,
and floats. 

L<http://www.c2.com/cgi/wiki?NoseJobRefactoring> - an extreme case of the
utility of strong types.

L<Class::Contract>, by Damian Conway

L<Attribute::Types>, by Damian Conway

L<Sub::Parameters>, by Richard Clamp

L<Object::PerlDesignPatterns>, by myself. 

The test.pl file that comes with this distribution demonstrates exhaustively
everything that is allowed and everything that is not. 

=head1 AUTHOR

Scott Walters - scott@slowass.net

=head1 COPYRIGHT

Distribute under the same terms as Perl itself.

=cut

__END__

  # my FooBar $bar :typed = 1 and any number of other compound constructs

  # r     <2> sassign vKS/2 ->s
  # f        <$> const(IV 1) s ->g                   <-- assign from
  # q        <@> list sKRM*/128 ->r                  <-- assigned to
  # g           <0> pushmark vRM* ->h                     <-- what targ ultimately falls through?
  # o           <1> entersub[t4] vKS*/DREFSV ->p
  # h              <0> pushmark s ->i
  # i              <$> const(PV "attributes") sM ->j
  # j              <$> const(PV "FooBar") sM ->k
  # l              <1> srefgen sKM/1 ->m
  # -                 <1> ex-list lKRM ->l
  # k                    <0> padsv[$bar:493,494] sRM ->l
  # m              <$> const(PV "typed") sM ->n
  # n              <$> method_named(PVIV 1878035063) ->o
  # p           <0> padsv[$bar:493,494] sRM*/LVINTRO ->q  <-- okey, kind of an obvious question in this case

  # XXX this doesn't work - $targ doesn't represent a known typeob - because
  # our parser hasn't made it there yet! we're too early. have to add "when defined" hooks
  # onto types - a sub reference to be executed when they are finally defined, to go
  # back and investigate the last use of that type, should it be defined. this would
  # need to go into a seperate hash or muck up a lot of "if $scalars->{x}" tests.

  if($self->name() eq 'list' and
     $self->last()->name() eq 'padsv' 
  ) {
    print "debug: list/padsv\n" if $debug;
    my $targ = $self->last()->targ();
    return get_arg_ob(lookup_targ($targ), 'okey') if lookup_targ($targ);
    print "debug: list/padsv: undef - targ: $targ name: ", lexicalname($targ), "\n" if $debug;
    get_arg_ob(undef, "non-type-checked scalar: '" . lexicalname($targ) . '"');
  }

----------

we have to watch for the initial declaration of a variable, so that we can
associate its pad slot (targ) with the little data container object we
cooked up for that variable.

2     <;> nextstate(main 494 test.pl:32) v ->3
d     <@> list vK/128 ->e
3        <0> pushmark v ->4
b        <1> entersub[t2] vKS*/DREFSV ->c
4           <0> pushmark s ->5
5           <$> const(PV "attributes") sM ->6
6           <$> const(PV "FooBar") sM ->7
8           <1> srefgen sKM/1 ->9
-              <1> ex-list lKRM ->8
7                 <0> padsv[$foo:494,496] sRM ->8
9           <$> const(PV "typed") sM ->a
a           <$> method_named(PVIV 1878035063) ->b
c        <0> padsv[$foo:494,496] vM/LVINTRO ->d


assigns will look like one of:

w     <2> sassign vKS/2 ->x
u        <1> entersub[t5] sKS/TARG ->v
r           <0> pushmark s ->s
s           <$> const(PV "FooBar") sM/BARE ->t
t           <$> method_named(PVIV "new") s ->u

or:

10    <2> sassign vKS/2 ->11
y        <0> padsv[$foo:192,194] s ->z
z        <0> padsv[$bar:193,194] sRM* ->10

(both cases assume lexicals)

------------

Oh. SVs know what stash they're in. Very very handy!

    if($op->name eq 'padsv') {
        my $target = (($cv->PADLIST->ARRAY)[0]->ARRAY)[$op->targ];
        if(UNIVERSAL::isa($target,'B::SV') && $target->FLAGS & SVpad_TYPED) {
            $typed{$cv->ROOT->seq}->{$op->targ}->{type} = $target->SvSTASH->NAME;
            $typed{$cv->ROOT->seq}->{$op->targ}->{name} = $target->PV;
        } elsif(UNIVERSAL::isa($target,'B::SV') &&
                exists($typed{$cv->ROOT->seq}->{$target->PV})) {
            $typed{$cv->ROOT->seq}->{$op->targ} = $typed{$cv->ROOT->seq}->{$target->PV};
        }
    }

------------

  # DumpArray(($curcv->PADLIST->ARRAY)[1]->ARRAY); # heh, fun

      print +(($curcv->PADLIST->ARRAY)[1]->ARRAY)[$self->first()->targ()]->sv(); # even better - the last IV points to $foo!

in lexicalref() :
  # return B::RV::RV((($curcv->PADLIST->ARRAY)[1]->ARRAY)[$targ]); # somehow bypasses $foo and goes to the array $foo references
  # return (($curcv->PADLIST->ARRAY)[1]->ARRAY)[$targ]->RV(); # this gets us a reference to the array $foo refers to - better
  # also
  # return (($curcv->PADLIST->ARRAY)[0]->ARRAY)[$targ];  # sub-zero is the meta inf for this pad slot - lexical name, etc
  #return B::RV::RV($thing);
  # while(B::class($tmp) eq 'RV') { $tmp = $tmp->RV(); }

      # print "testing: trying to extract RV then IV: ", lexicalref($self->first()->targ()), "\n";
      # print "testing: trying to extract RV then IV: ", lexicalref($self->first()->targ())->RV()->RV(), "\n";
      # print "testing: trying to extract RV then IV: ", lexicalref($self->first()->targ())->RV()->int_value(), "\n";

to get a name out of a pad:

    } elsif ($h{targ}) {
        my $padname = (($curcv->PADLIST->ARRAY)[0]->ARRAY)[$h{targ}];
        if (defined $padname and class($padname) ne "SPECIAL") { 
            $h{targarg}  = $padname->PVX;
            my $intro = $padname->NVX - $cop_seq_base;
            my $finish = int($padname->IVX) - $cop_seq_base;
            $finish = "end" if $finish == 999999999 - $cop_seq_base;
            $h{targarglife} = "$h{targarg}:$intro,$finish";
        } else {
            $h{targarglife} = $h{targarg} = "t" . $h{targ};
        }
    }

      # my $tmp = B::svref_2object(lexicalname($self->first()->targ()));
      # print "trying to locate the referenced value: ", $tmp->name(), "\n";

  # return $padname->NAME(); # doesn't exist - the method doesn't
  # return $padname->RV(); # not a reference value. humpf.

------------

attributes:

scalars:

package FooBar;
use typesafety;

# methods:
# same as: use attributes 'FooBar', \&foo, 'safe';
sub foo :safe {
}

# scalars:
# same as: use attributes 'FooBar', \my $foo, 'safe';
package main;
my FooBar $foo :safe;

in these two examples, the FooBar class woud inherit MODIFY_SCALAR_ATTRIBUTES
and MODIFY_CODE_ATTRIBUTES from TypeSafety. attribute.pm passes requests to
these (and other type dependent methods) for unknown attributes. TypeSafety
would need only record which reference was of which type ($foo is a FooBar,
\&FooBar::foo returns a FooBar, etc).

at CHECK time, the op tree is inspected for assignments. all assignments must be
from either safe methods or safe scalars to safe scalars. initially, lvalues and
operator overloading would be ignored and doomed to failure. rules similar to
java would be applied: the thing on the right must be an isa() of the thing on
the left. the actual scalar reference and sub wouldn't be itself blessed,
but instead the ISA checks would be done on whatever types were given to attribute.

------

Perl stores an amazing amount of data in the bytecode tree. This makes
static analysis both a joy and a fertile field of study. 

Source filters can do some things that the B modules can't. L<Acme::Bleach>
operates on something radically different than Perl. L<Sub::Lexical>
extends the syntax beyond what Perl is capable of.
See L<Filter::Simple> for information on source filters.

See perldoc B and L<B::Generate> for more information on Perl's bytecode
interpreter, B.

---------------------------

processing return statements:

r     <;> nextstate(main 564 test.9.pl:32) v ->s
y     <@> return K ->z
s        <0> pushmark s ->t
t        <0> padsv[$bar:563,564] ->u          # $bar
u        <$> const(IV 10) s ->v               # 10
x        <1> entersub[t5] KS/TARG,1 ->y       # bar()
-           <1> ex-list K ->x
v              <0> pushmark s ->w
-              <1> ex-rv2cv sK/1 ->-
w                 <$> gv(*bar) s ->x
z     <;> nextstate(main 564 test.9.pl:34) v ->10

---------------------------

processing closures:

lightbright# perl -MO=Concise -e 'sub { print "hi\n"; }->();'
8  <@> leave[&:-586,-588] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 2 -e:1) v ->3
7     <1> entersub[t2] vKS/TARG,1 ->8
-        <1> ex-list K ->7
3           <0> pushmark s ->4
-           <1> ex-rv2cv K/1 ->-
6              <1> refgen sK/1 ->7
-                 <1> ex-list lKRM ->6
4                    <0> pushmark sRM ->5
5                    <$> anoncode[CV ] lRM ->6

anoncode's t_arg is a pointer to code - an op perhaps even?

------

from types.pm:

    if(ref($op) eq 'B::PADOP' && $op->name eq 'gv') {
#       $op->dump;
        my $target = (($cv->PADLIST->ARRAY)[1]->ARRAY)[$op->padix];
#       $target->dump;
#       exit;
    }


-------

# this was in the first version:

use attributes;

sub MODIFY_SCALAR_ATTRIBUTES {
  # this, like declare()'s definition above, does nothing when executed, but
  # generates signiture code in the bytecode tree. it is this signiture that
  # we recognize and extract information from.
  return () if $_[2] eq 'typed'; # success
  return undef;                  # don't know that attribute, sorry
}

  # my FooBar $foo :typed;

  # 2  <;> nextstate(main 514 test.pl:32) v
  # 3  <0> pushmark v
  # 4  <0> pushmark s
  # 5  <$> const(PV "attributes") sM      --- we start scanning here
  # 6  <$> const(PV "FooBar") sM
  # 7  <0> padsv[$foo:514,516] sRM
  # 8  <1> srefgen sKM/1
  # 9  <$> const(PV "typed") sM
  # a  <$> method_named(PVIV 1878035063) 
  # b  <1> entersub[t2] vKS*/DREFSV       --- and stop here
  # c  <0> padsv[$foo:514,516] vM/LVINTRO
  # d  <@> list vK/128

  if($self->name() eq 'const') {
    # go on the lookout for type checked variable definitions
    # we record the pad and name of variables defined using our little type specifying idiom
    # this is needed so that we can relate pad information to name/package/type/etc
    # lookup_targ() now tries to set up new variables that are otherwise undefined.
    my $op = $self;
    my $pad; my $type; 
    # print "debug: entersub - looking for pad info for my() syntax - going in, line $lastline...\n";
    foreach my $test (
      sub { $op->name() eq 'const' and $op->sv()->sv() eq 'attributes'  },   # "attributes"
      sub { $op->name() eq 'const' and $type = $op->sv()->sv()  },           # "FooBar" - type information
      sub { $op->name() eq 'padsv' and $pad = $op->targ()  },  
      sub { $op->name() eq 'srefgen' },
      sub { $op->name() eq 'const' and $op->sv()->sv() eq 'typed'  },        # "typed" - attribute name
      sub { $op->name() eq 'method_named' },
      sub { return unless $op->name() eq 'entersub'; associate_scalar($pad, $type); },
    ) {
       # print "debug: considering: looking for pad info: ", $op->name(), "\n";
       last unless $test->(); 
       $op = $op->next() or last; # using next() here, not sibling(), on purpose 
    }
  }

----------

  # declare FooBar => my $test3;

  # l  <;> nextstate(main 581 test.3.pl:25) v
  # m  <0> pushmark s                            <--- start scanning here
  # n  <$> const(PV "FooBar") sM/BARE
  # o  <0> padsv[$test3:581,582] lM/LVINTRO
  # p  <$> gv(*declare) s
  # q  <1> entersub[t5] vKS/TARG,1
  # r  <;> nextstate(main 582 test.3.pl:27) v

  if($self->name() eq 'pushmark') {
    # go on the lookout for type checked variable definitions
    # we record the pad and name of variables defined using our little type specifying idiom
    # this is needed so that we can relate pad information to name/package/type/etc
    my $op = $self;
    my $pad; my $type; 
    # print "debug: entersub - looking for pad info for declare() syntax - going in, line $lastline...\n";
    foreach my $test (
      sub { $op->name() eq 'pushmark' },
      sub { $op->name() eq 'const' and $type = $op->sv()->sv()  },           # "FooBar" - type information
      sub { $op->name() eq 'padsv' and $pad = $op->targ()  },  
      sub { $op->name() eq 'gv' and ($op->sv()->sv() eq 'declare' or $op->sv()->sv() =~ m/::declare$/) }, # "declare"
      sub { return unless $op->name() eq 'entersub'; associate_scalar($pad, $type);  },
    ) {
      # print "debug: looking for pad info: considering: ", $op->name(), "\n";
      last unless $test->(); 
      $op = $op->next() or last; # doing next() on purpose, not sibling()
    }
  }

-----------------------

package FooBar; 
use typesafety; 
package main; 
use typesafety; 
(declare FooBar => my $test5) = 10;

c  <@> leave[$test5:525,526] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 525 -e:1) v ->3
b     <2> aassign[t3] vKS ->c
-        <1> ex-list lK ->5
3           <0> pushmark s ->4
4           <$> const(IV 10) s ->5
-        <1> ex-list lK ->b
5           <0> pushmark s ->6
a           <1> entersub[t2] lKPRMS*/NO(),TARG,1 ->b
-              <1> ex-list lK ->a
6                 <0> pushmark s ->7
7                 <$> const(PV "FooBar") sM/BARE ->8
8                 <0> padsv[$test5:525,526] lM/LVINTRO ->9
-                 <1> ex-rv2cv sK/129 ->-
9                    <$> gv(*declare) s ->a

------

  # more old, retired original code

  sub associate_scalar {

    my $pad = shift;   # pad slot number
    my $type = shift;  # litteral name of the type

    lookup_targ($pad) and
      confess lexicalname($pad) . ' already defined: first declaration: ' . $scalars->{$pad}->diagnostics() . ' ' . 
          ' second declaration: ' . nastily;

    $scalars->{$pad} = get_type_ob($type, $lastpack, $lastfile, $lastline, $pad, lexicalname($pad), 'variable');
    # print "debug: success - found pad of variable ", $scalars->{$pad}->name(), " - pad $pad, at file $lastfile line $lastline\n";
  }

-------

# sub foo (int $la, string $bar) {
# }

    if($cv->FLAGS & SVf_POK && !$function_params{$cv->START->seq}) {
        #we have, we have, we have arguments
        my @type;
        my @name;
        my $i = 1;
        foreach (split ",", $cv->PV)  {
            my ($type, $sigil, $name) = split /\b/, $_;
        #    print "$type - $sigil - $name \n";
            push @type, $type;
            if($sigil && $name)  {
                push @name, $sigil.$name;
                $typed{$cv->ROOT->seq}->{"$sigil$name"}->{type} = $type;
                $typed{$cv->ROOT->seq}->{"$sigil$name"}->{name} = $sigil.$name;
            } else {
                push @name, "Argument $i";
            }
            $i++;
        }

        $function_params{$cv->START->seq}->{name} = \@name;
        $function_params{$cv->START->seq}->{type} = \@type;


        #print $cv->PV . "\n";
        $cv->PV(";@");

    }



