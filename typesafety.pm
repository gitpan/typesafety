package typesafety;

#
# simple static analisys, using the B backend.
#

# where we left off:

# major outstanding issues - see Bugs in the POD

# o. more method argument handling and bless idioms.
#    unshift on @_ should generate typeobs based on what unshift_prototype() has to say.
#    $_[0] should generate typeobs based on what aelem_prototype() has to say.
# o. rather than one huge sequence of if statements, solve_type() should dispatch based on
#    op name and/or other information. this is getting massive. a pattern is starting to
#    emerge - most ops just do solve_type(), solve_list_type(), enforce_type(), or enforce_list_type()
#    in some combination on some combination of the first(), last(), and first()->sibling()
#    with different error messages provided where enforce* methods are used.
# o. types.pm allows method prototypes like sub foo (int $bar, string $baz) - amazing! how? steal!
#    insert code into the op tree to create scalars and read arguments specified in the prototype ().

# maybe outstanding issues:

# o. check_args() does: goto OKEY if $rightob->type()->isa($left); - $left is just a string,
#    like FooBar. perhaps it would be helpful to keep a special hash of typeobs by package.
#    the typeob would be a default generic typeob representing the return type of the constructor,
#    not any specific method. in fact, not even that specific, but i can't think of any existing
#    typeob we have floating around more generic.
# o. everything depends on having a pad slot right now - this should be generalized to
#    handle locals. 
# o. private, public, protected, friend protection levels, as well as static. non-static
#    methods aren't callable in packages specified by const, only via padsvs and
#    such. eg, FooBar->bleah() must be prototyped static if prototyped. non-static methods
#    should get a $this that they can make method calls in and has type inferred by how it
#    was used (if $foo->bar() is called, and bar() calls $this->baz(), the type comes from 
#    what $foo was prototyped to hold).
# o. just for fun, we should use ourself (or a copy of ourself) on ourself. we should examplify the code style
#    we're proposing other people use.
# o. lvalues might just work right now - think about it and test. solve_type() hung off of an
#    sassign where substr() evaluates to 'string' would work, for example.
# o. if more than once instance of a given
#    type appears in a row as the last type in an argument list prototype, we can assume that the
#    array will take care of it. P6's globbing symmantics would be useful.
# o. use canned_type('unknown') in more places - atleast default where the context isn't void
# o. OPf_STACKED.
# o. what exactly is padix?
# o. mangle function names using source filters and do method overloading based on those mangled names?
# o. check_types() should be used more often. i think it could remove a lot of code.
# o. litteral type names in strings - eg, arguments to bless. we might have to track data
#    with completely different heuristics and intentions to see if the first arg to a 
#    constructor gets converted from a possible object reference to a string and then
#    winds up being used as the second arg to bless. argh.
# o. OPf_STACKED on an op at the current root level means that the previous root level
#    op (and things under it) should be typechecked as an input for the first arg rather than 
#    something under it - i think.
# o. something like solve_list_type(), but rather than trying to find the value of everything
#    (as is appropriate for list assignments, argument construction to things like grep, etc),
#    just find the common type from the fall through value and any return values.
#    "a closure, method, subroutine, eval block, or similar was found."
#    this is tricky - we'd have to hack up solve_type() to distinguish between possibly
#    downward propogated types and things that really fall through and return.
#    perhaps a flag in typeob that indicates a calculated type is a returned/last in block.
#    a real understanding of perl's internal stacks and the ops that minipulate them is
#    what is really needed.

# major resolved issues:

# v/ 'return' returns to enclosing method/subroutine call, not the op above it - $expected
#    only tells the type the above op expects! bug! need another currently expected type for
#    the method call. bug!
# v/ arrays- they need to be able to refer to a history of types expected of
#    that type (things assigned *from* it) and a history of things assigned to it.
#    should an inconsistency arise between what is assigned to and what is assigned from,
#    report diagnostics on both. this means that we could assign any type of object and
#    all kinds of non-objects to an array with no problem, until the array is actually
#    used as the source for some type.
#    array pad slots, alem should typecheck to the type of the array
#    ML-style automatic argument type discerning?
#    explicit type-case analysis on a shift etc from an array might be checkable to make sure
#    that all possible array contents types are accounted for in the explicit type-case check.
#    ->type() on an untyped scalar or array that has things in its accept list should return
#    the common type of that list. XXX - this only considers things assigned to the array,
#    not things expected of it, right now. the latter logic could be useful if no information
#    about what is being assigned to it is visible at the time ->type() is called. 
#    ooo need support for shift, pop, unshift, push, grep, map, alem, and so forth
# v/ some array idioms are in place but are untested.
#    need a shift/aassign idiom for reading method arguments - badly.
#    incoming arguments to a method are checked for type, but we lose track of that type
#    going from one CV to another. minimally, two idioms must be recognized:
#    my $foo = shift and my($a, $b, $c) = @_
#    these should fix up the $scalars database, associating the new targs with elements
#    of the method prototype. shift would step through the prototype one thing at a time,
#    advancing to the next each time the idiom is seen. the array assignment would do
#    the whole thing at once. more generally, arrays could be considered to be prototyped
#    just like methods, in addition to just having inferred types. some arrays would
#    be big bags of a base type, others would be sequences of different types.
#    type check incoming arguments as they're used - $_[0], $_[1], $_[2], shift @_, pop @_
#    should all get this treatment. used with a prototype naming actual variables, this
#    gets cleaner.
# v/ need a special typeob to represent "no type at all", such as nextstate would give.
#    need special typeobs to represent int, float, and string.
# v/ there is some confusion between when to pass actual types down or expected types up.
#    from a comment:
#    we currently make no attempt to validate the result type - instead, the expected type is
#    propogated up. this is because solve_list_type() on a raw CV returns a lot of garbage from
#    ops it doesn't understand, whereas propogating it up gives better diagnostics and only
#    checks when and were appropriate.
#    oooh, and it gets worse. sometimes an assignment returns nothing (or its return value isn't used).
#    other times, it is. we have no way of knowing that i can think off. i guess $expected shouldn't
#    propogate so readily.
# v/ if, while, if/elsif/else, foreach, for... we aren't getting into the bodies of these
#    constructs. lineno.pm started to do this.
# v/ array, scalar, and void contexts could tell us whether or not $expected should be set.
#    in perl, pp_wantarray looks something like:
#       cxix = dopoptosub(cxstack_ix);
#       switch (cxstack[cxix].blk_gimme) 
#    is there something in a CV that specifies this? seems like the granularity would be much finer
# v/ argobs must die. all this if($argob->type()) stuff is bullshit. proposal: flag in typeob
#    to indicate whether it is an object or primitive type. clone() method so that diagnostics
#    can be added to types found other routes.
# v/ should call lookup_targ every time we find any sort of pad just so they get defined.
# v/ $scalars entries must be qualified by $curcv
# v/ we should observe *any* unsafe use of scalars we've defined - that means picking raw padsv's out of
#    the blue in the bytecode tree, and warning or dieing. likewise, we should descend through any
#    unknown ops or known ops used on non-type-checked things. should track expected return type, too.
# v/ we must descend into any code references we see defined. they should be pushed onto a 
#    queue, sort of like %knownuniverse.
# v/ functions should be prototyped too - package would obviously default to current package.
# v/ decyphering lists for the padsv on the end still doesn't work. my FooBar $foo :typed = 1; happily runs.
# v/ should we clear $scalars between calls to different methods? i think Perl reuses the pad numbers, so yes.
# v/ we should propogate expected type up as we recurse, if any, or else undef 
#    to make sure that nothing dies for lack of type data when we're just exploring the tree.
#    we're already narrowing down offending code to the statement, but propogating the
#    type information up would narrow it down to the exact place in the expression that
#    type safety was lost. reporting on the top and bottom would be most useful -
#    if a method argument is wrong and it comes from an expression, which arg has the
#    wrong type and at what point in the expression might both be useful. not sure what
#    i'm going to do with this. $expected in solve_type().
# v/ return statements themselves! how could i forget. this whole project was both more complex
#    and easier than expected. easier to do individual things but more things to do. in side of
#    a code block (the loop in check()), if there is a prototype for the code block we're
#    currently doing, make sure all return statements return something of that type.
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
our $VERSION = '0.03';

use B;
use B::Generate;

#
# constants
#

use B qw< ppname >;
use B qw< OPf_KIDS OPf_STACKED OPf_WANT OPf_WANT_VOID OPf_WANT_SCALAR OPf_WANT_LIST >;
use B qw< OPpTARGET_MY >;
use B qw< SVf_IOK SVf_NOK SVf_POK SVf_IVisUV >;
sub SVs_PADMY () { 0x00000400 }     # use B qw< SVs_PADMY >;

#
# er, variable
#

my %knownuniverse; # all known namespaces - our inspection list
my %args;          # use-time arguments
my $debug = 0;     # debug mode flag
our $curcv;        # codevalue to get pad entries from
our $returnvalue;  # typeob expected of returns, if any

my $lastline; my $lastfile; my $lastpack;  # set from COP statements as we go 

#
# debugging
#

use Carp 'confess', 'cluck';
use B::Concise 'concise_cv';

sub debug { my @args = @_; my $line = (caller)[2]; print "debug: $line: ", @args, "\n" if $debug; }

sub nastily () { " in package $lastpack, file $lastfile, line $lastline"; }

# $SIG{__DIE__} =  $SIG{INT} = sub {
#    # when someone does kill -INT <our pid> from the command line, dump our stack and exit
#    print STDERR shift, map { (caller($_))[0] ? sprintf("%s at line %d\n", (caller($_))[1,2]) : ''; } 0..30;
#    print STDERR join "\n", @_;
#    exit 1;
# };

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
     define_method($caller, $method, 
        typesafety::methodob->new(
          type=>$type, package=>$caller, filename=>$filename, line=>$line, 
          name=>$method, desc=>'prototyped method', takes=>$takes,
        )
     );
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
  my $scalars;       # $scalars->{$curcv}->{$targ} = typeob

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

    return $scalars->{$curcv}->{$targ} if exists $scalars->{$curcv} and exists $scalars->{$curcv}->{$targ};

    # assume first usage and infer type if possible
    # record that for future lookup

    my $name = (($curcv->PADLIST->ARRAY)[0]->ARRAY)[$targ];  # from B::Concise

    # from perlguts:
    #        One can deduce that an SV lives on a scratchpad by looking on its flags: lexicals
    #        have "SVs_PADMY" set, and targets have "SVs_PADTMP" set.
    # this doesn't seem to be accurate - doing my WrongType $wt2, this claims that $wt2 isn't PADMY

    # debug("lookup_targ: ", $name->sv(), " is not a PADMY") unless $name->FLAGS() & SVs_PADMY;
    # return undef unless $name->FLAGS() & SVs_PADMY;

    # $name is a PVMG - a magic pointer. perlguts illustrated at http://gisle.aas.no/perl/illguts/ has to say about PVMGs:
    # The SvPVMG is like SvPVNV above, but has two additional fields; MAGIC and STASH. MAGIC is a pointer to additional 
    # structures that contains callback functions and other data. ...  STASH (symbol table hash) is a pointer to a HV 
    # that represents some namespace/class. (That the HV represents some namespace means that the NAME field of the HV 
    # must be non-NULL. See description of HVs and stashes below). The STASH field is set when the value is blessed into 
    # a package (becomes an object). The OBJECT flag will be set when STASH is. (IMHO, this field should really have 
    # been named "CLASS". The GV and CV subclasses introduce their own unrelated fields called STASH which might be confusing.)

    return undef unless $name->can('SvSTASH') and $name->SvSTASH;
    my $type = $name->SvSTASH->NAME; 

    # "main" is the default type should no other type be specified. we're only intersted in scalars that have types
    # specified, for now. eg: my FooBar $foo. later, though, we may attempt to track all of the different things expected of a scalar
    # in the default package and everything assigned to it. arrays, too.

    return undef unless $type and $type ne 'main';

    # since we've never seen this lexical in this context before, we assume that it is new, and this is its first
    # usage. record the information for the current point in the perl program we're crawling.

    return $scalars->{$curcv}->{$targ} = typesafety::scalarob->new(
        type=>$type, package=>$lastpack, filename=>$lastfile, line=>$lastline, pad=>$targ, name=>$name->sv(),
        desc=>'scalar variable named',
    );

  }

  sub lookup_array_targ {
    # this is used on arrays - we can't hope to find type information for, but we want to
    # keep a record of it anyway. still must be lexical.
    my $targ = shift;
    return lookup_targ($targ) if lookup_targ($targ);
    my $ret = $scalars->{$curcv}->{$targ} = typesafety::arrayob->new(
        pad=>$targ, name=>lexicalname($targ), desc=>'array variable named',
    );
    $debug and print "debug: ", __LINE__, ": lookup_array_targ: created this: ", $ret->diagnostics(), "\n";
    return $ret;
  }
  
  sub summary {
    # give a nice report of what we did
    print "typesafety.pm status report:\n";
    print "----------------------------\n";
    foreach my $cv (values %$scalars) {
      foreach my $typeob (values %$cv) {
        print $cv->diagnostics(), "\n";
      }
    }
  }

  my $cannedtypes = {
    none      => typesafety::typeob->new(type => 'none',     desc => "construct doesn't return any value at all"), 
    unknown   => typesafety::typeob->new(type => 'unknown',  desc => "construct returns a value - probably - but what, we aren't sure"),
    constant  => typesafety::typeob->new(type => 'constant', desc => 'constant value'), 
    int       => typesafety::typeob->new(type => 'int',      desc => 'integer value'),  
    float     => typesafety::typeob->new(type => 'float',    desc => 'floating point value'), 
    string    => typesafety::typeob->new(type => 'string',   desc => 'string value'), 
  };

  *canned_type = sub {
     confess unless exists $cannedtypes->{$_[0]};
     return $cannedtypes->{$_[0]};
  };

}

#
# verify that types are what the user specified
#

sub check {

  # this is the heart of this module.
  # we grok the bytecode, looking for signiture pattern, and extract information
  # from them. when a pattern is found, we update internal information, or
  # else test internal information to see if something is "safe".

  $returnvalue = undef;

  # check the main area first - it may set things up that are in the scope of methods defined later
  $curcv = B::main_cv();
  solve_list_type(B::main_root()->first(), undef);

  # each package that has used us, check them as well

  foreach my $package (keys %knownuniverse) {
    foreach my $method (grep { defined &{$package.'::'.$_} } keys %{$package.'::'}) {

      next if $method eq 'proto';
      next if $method eq 'declare';

      # return statements out of methods are expected to return a certain type, as are fall-through values.

      # debug("knownuiverse: method: $method");

      my $cv = *{$package.'::'.$method}{CODE};
      $curcv = B::svref_2object($cv);
      B::svref_2object($cv)->ROOT() or die;

      $debug and concise_cv(0, $cv); # dump the opcode tree of this code value

      my $expected = lookup_method($package, $method);

      debug("method is prototyped as: ", $expected ? $expected->diagnostics() : 'not prototyped');

      $returnvalue = $expected;     # $expected changes as we go down the op tree, but $returnvalue covers the whole method
      # shifts done on @_ return objects typed consistent with the prototype
      $expected->reset_prototype() if $expected; 

      # enforce_list_type(B::svref_2object($cv)->ROOT()->first(), $expected, 'method return type is prototyped');
      solve_list_type(B::svref_2object($cv)->ROOT()->first(), $expected);

    }
  }

  summary() if(exists $args{summary}); 

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

  # $expected, the second arg, changes our role from merely solving which type something
  # returns to enforcing that things return that type. we're able to more intelligently
  # do this than something looking at our return data.

  # failure dies. 
  # success returns typesafety::argob object representing the result and the where 
  # bytetree scanning left off.
  # success is easily won when no particular type is expected.

  my $self = shift;
  my $expected = shift;

  my $want = $self->flags() & OPf_WANT;

  $debug && $expected and print "debug: ", __LINE__, ": expected true going into solve_type(): ", $expected->diagnostics(), "\n";

  debug('solve_type: op: ', $self->name());

  #
  # XXXX 
  #

  if($want == OPf_WANT_VOID) {
    # highly experimental XXX
    # if we impose void context, then we and none of our children can or will return anything. 
    # if we're trying to solve a list, then this op just doesn't contribute to this list - not undef, nothing. 
    $expected = undef;
  }

  #
  # simple and recursive
  #

  # null - ops that were optimized away

  if($self->name() eq 'null' and
     $self->can('targ') and
     $self->flags & OPf_KIDS and
     $self->first() 
  ) {
    $debug and print "debug: ", __LINE__, ": null type: ppname: ", $self->can('targ') ? ppname($self->targ()) : 'unknown', "\n";
    $debug and print "debug: ", __LINE__, ": null op has kids, first is: ", $self->first()->name(), "\n";
    # $debug and print "debug: ", __LINE__, ": null op has kids, second is: ", $self->first()->sibling()->name(), "\n";
    return solve_type($self->first(), $expected);
  }

  # c           <|> cond_expr(other->d) lK/1 ->h
  # b              <2> modulo[t3] sK/2 ->c
  # 9                 <1> int[t2] sK/1 ->a
  # 8                    <1> rand[t1] sK/1 ->9
  # 7                       <$> const(IV 5) s ->8
  # a                 <$> const(IV 2) s ->b
  # d              <$> const(PV "hi") s ->e
  # h              <$> const(PV "there") s ->e

  if($self->name() eq 'cond_expr') {
    # an if() or ? : - the condition doesn't return anthing but should be examined for buried use of types.
    # the two blocks must both return the expected type, if any. yes - there are always two blocks -
    # if there were only one, this would be reduced to an 'and' instruction.
    # XXX - in the case of if(0), only the second block should be checked, and if(1), only the first.
    solve_type($self->first(), undef);
    enforce_type($self->first()->sibling(), $expected);
    enforce_type($self->first()->sibling()->sibling(), $expected);
  }

  # for(my $i = 1..20) { print $i, "\n"; }

  # j     <2> leaveloop vK/2 ->k
  # a        <{> enteriter(next->g last->j redo->b) lK ->h
  #             ..... condition goes here
  # -        <1> null vK/1 ->j
  #             ..... body goes here

  if($self->name() eq 'leaveloop') {
    # we don't expect that a for() loop returns anything, but we should check inside of it and the conditional.
    # which is the first thing at the beginning of the body. how bizarre.
    check_list_type($self->first(), undef); 
    check_list_type($self->first()->sibling(), undef); 
  }

  if($self->name() eq 'and') {
    enforce_type($self->first(), undef);
    enforce_type($self->first()->sibling(), $expected);
  }

  if($self->name() eq 'or') {
    enforce_type($self->first(), $expected);
    enforce_type($self->first()->sibling(), $expected);
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

    return canned_type('none');

  }

  if($self->name() eq 'pushmark') {
    return canned_type('none');
  }

  # const

  if($self->name() eq 'const') {
    # very simple case
    debug('const');
    return canned_type('constant')->clone(sprintf q{'%s', }, $self->sv()->sv());
  }

  # lexicals

  if($self->name() eq 'padsv') {
    # simple case
    # $debug and print "debug: ", __LINE__, ": padsv\n";
    # this happens when we see non-typesafe scalars, which we tolerate ;)
    return lookup_targ($self->targ()) ||
      typesafety::scalarob->new(type=>'none', desc=>'non-type-checked scalar', pad=>$self->targ(), name=>lexicalname($self->targ()));
  }

  if($self->name() eq 'padav') {
    # array on the pad
    # it will never happen that we find type info for an array - perl doesn't allow this. we must infer types.
    for(lookup_array_targ($self->targ())) {
      debug("padav: official type: ", $_ ? $_->type() : 'no type info');
      debug("padav: type of typeob object found: ", $_ ? ref($_) : 'none found');
    }
    return lookup_array_targ($self->targ()) ||
      typesafety::arrayob->new(type=>'none', desc=>'non-type-checked array', pad=>$self->targ(), name=>lexicalname($self->targ()));
  }

  # stacked - XXX - todo

  if($self->flags() & OPf_STACKED) {
    # XXX
    debug("oh, by the way, found an BINOP that is STACKED: ", $self->name());
  }

  #
  # return
  #

  # return 1, 2, 3, 4;

  # 8     <@> return K ->9
  # 3        <0> pushmark s ->4
  # 4        <$> const(IV 1) s ->5
  # 5        <$> const(IV 2) s ->6
  # 6        <$> const(IV 3) s ->7
  # 7        <$> const(IV 4) s ->8

  if($self->name() eq 'return') {
    # the pushmark seems to always be there - even on an empty return. yes, the return op has the needs mark bit in ops.h/opcodes.pl.
    # individual items in the list vary, of course.
    # return is special because each and every return's type must jive with the methods prototyped type. 
    # my $return = solve_list_type($self->first()->sibling(), $returnvalue);
    debug("return: expecting ", $returnvalue->diagnostics()) if $returnvalue;
    return enforce_list_type($self->first()->sibling(), $returnvalue, 'improper return value');
  }

  #
  # shift, push, pop, unshift, alem, etc
  # 

  # XXX - track which types are assigned, shifted, pushed, spliced into/onto arrays

  # d        <2> aelem sK/2 ->e
  # b           <0> padav[@a:1,2] sR ->c
  # c           <$> const(IV 1) s ->d

  # b        <1> shift sK/1 ->c
  # a           <0> padav[@a:1,3] lRM ->b

  if($self->name() eq 'shift' or $self->name() eq 'pop' or $self->name() eq 'aelem') {

    # dumb case - the array is our single child.   
    # this should be redundant with the generic UNOP/BINOP/LISTOP handling at the end - is it? almost - we propogate $expected,
    # but the generic case should too! XXX

    debug("aelem/pop/shift: we've decided the array type is: ", solve_type($self->first())->diagnostics());

    return enforce_type($self->first(), $expected, 'wrong array type');

  }

  if($self->name() eq 'aelemfast') {{
    # index is in ->private(), the array itself in ->sv(). how so very CISC. 
    # aelemfast will never reference a pad - aelem will happily accept a padav, though. this is only useful
    # for accessing method arguments.
    # few! this works - gv() does all of the padix() magic for us
    # debug("aelemfast: gv stash name: ", $self->gv()->STASH()->NAME()   );  # main
    # $returnvalue is the typeob for the current method, constructed from the method prototype. it contains
    # the list of types we accept as arguments.
    last unless $returnvalue;
    last unless $self->gv()->NAME() eq '_'; # as in @_
    my $typename = $returnvalue->aelem_prototype($self->private());
    $typename or die "argument to this method in position " . $self->private() . " has no prototype data" . nastily;
    my $typeob = lookup_method($typename, 'new'); # XXX - lookup_method() needs to autovivicate 'new' or else we need a seperate type-only index
    return $typeob || typesafety::typeob->new(type=>$lastpack, desc=>'assumed constructor return type');
  }}

  # h     <@> push[t7] vK/2 ->i
  # e        <0> pushmark s ->f
  # f        <0> padav[@a:1,3] lRM ->g   <-- array type, here only
  # g        <0> padsv[$b:2,3] l ->h     <-- list type, here on down

  if($self->name() eq 'unshift' or $self->name() eq 'push') {

    # solve the type of the list after the first real arg; ->accept() that type into the array; return the type of the array

    my $arraytype = solve_type($self->first()->sibling()); 
    my $listtype = solve_list_type($self->first()->sibling()->sibling());
    $arraytype->accept($listtype);
    return $arraytype;

  }

  #
  # pattern match ops
  #

  if(ref($self) eq 'B::PMOP' and $self->pmreplroot() && ${$self->pmreplroot()}) {
    # s///e
    # a code block is attached to the pattern match operation. code adapted from types.pm.
    # substring
    # XXX untested, probably wrong
    # XXX multiple concurrent pads required - have to index $scalars by $curcv as well as $targ
    local $curcv = $self->pmreplroot(); 
    return solve_list_type($self->pmreplroot(), $expected);
  }

  #
  # closures 
  #

  # sub { print "hi\n"; }->();

  # 8  <@> leave[&:-586,-588] vKP/REFC ->(end)
  # 1     <0> enter ->2
  # 2     <;> nextstate(main 2 -e:1) v ->3
  # 7     <1> entersub[t2] vKS/TARG,1 ->8
  # -        <1> ex-list K ->7
  # 3           <0> pushmark s ->4
  # -           <1> ex-rv2cv K/1 ->-
  # 6              <1> refgen sK/1 ->7
  # -                 <1> ex-list lKRM ->6
  # 4                    <0> pushmark sRM ->5
  # 5                    <$> anoncode[CV ] lRM ->6

  # anoncode's t_arg is a pointer to code - a B op object perhaps even?

  if($self->name() eq 'anoncode') {
    # XXX untested
    solve_type($self->targ(), $expected);
  }

  #
  # real code and constructs
  #

  #
  # blessing and other constructor idioms
  # 

  # bless {}, "FooBar";

  # 7     <@> bless vK/2 ->8
  # -        <0> ex-pushmark s ->3
  # 5        <1> srefgen sK/1 ->6
  # -           <1> ex-list lKRM ->5
  # 4              <@> anonhash sKRM ->5
  # 3                 <0> pushmark s ->4
  # 6        <$> const(PV "FooBar") s ->7

  if($self->name() eq 'bless') {
    # first arg doesn't matter, though we could scream if it seems like something is being reblessed. 
    # reblessing would really muck up the works.
    # there is always a pushmark or ex-pushmark: ignore it. then the reference. then an optional type.
    my $op = $self->first(); 
    my $ref = denull($op->sibling());
    my $typeop = denull($op->sibling()->sibling());
    my $type;
    debug("bless: 2nd and 3rd args: ", $ref->name(), ' ', $typeop->name());
    if(! $$typeop) {
      # single argument bless defaults to blessing into current package
      $type = $lastpack;
    } else {
      $type = solve_lit($typeop); # - aelem and aelemfast and shift on @_
      $type or warn "typesafety.pm isn't currently able to infer the type of the about to be created" . nastily;
      $type or return canned_type('unknown')->clone('bless but not one of the supported idioms - I suck');
    }
    # XXX else, is this scalar a special one that contains ref $_[0]?
    return typesafety::typeob->new(type=>$type, package=>$lastpack, filename=>$lastfile, line=>$lastline, desc=>'type as returned by constructor');
  }

  #
  # method and function calls
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

     # is it a constructor call on a constant type? 
     # these are self-typing. abstract factories shouldn't use constructors for their dirty work.

     # print "debug: entersub (constructor?), line $lastline\n" if $debug;

     my $op = $self->first();

     # XXX this is probably needed in a thousand places in this program, not to mention recursive application
     $op = denull($op);

     my $type;
     my $success = 0;
     my $argop;

     foreach my $test (
       sub { $op->name() eq 'pushmark' },
       sub { return unless $op->name() eq 'const'; $type = $op->sv()->sv(); return 1; },
       sub {
         while($op->name() ne 'method_named' and $op->name() ne 'null') {
           # seek past method call arguments but remember the opcode of the first argument.
           $argop ||= $op;
           $op = $op->sibling();
         }
         return unless $op and $op->name() ne 'null'; 
         return unless $op->sv()->sv() eq 'new'; 
         $success = 1; 
         $debug and print "debug: success\n";
       },
     ) {
       debug("bar->new(): considering: ", $op->name());
       last unless $test->(); 
       $op = $op->sibling() or last;
     }

     if($success) {
       debug("success! found constructor for type $type");
       debug("but what we really want is a ", $expected->diagnostics()) if $expected;
       return check_args($argop, $type, 'new');
       # return lookup_method($type, 'new'); # just not the same thing for some reason - huh
     }

  }

  # package FooBar; foo('BazQux');

  #   `-<6>entersub[t1]---ex-list-+-<3>pushmark
  #                               |-<4>const(PV "BazQux")
  #                               `-ex-rv2cv---<5>gv(*FooBar::foo)

  # case, when the method is known and perl references the gv directly

  if($self->name() eq 'entersub') {

     my $op = denull($self->first());

     my $type;
     my $method;
     my $success = 0;
     my $argop;

     foreach my $test (
       sub { $op->name() eq 'pushmark' },
       sub {
         while($$op) {
           # seek past method call arguments but remember the opcode of the first argument.
           if($op->name() eq 'null' and ! ${$op->sibling()} and pppname($op) eq 'pp_rv2cv') {
             # no next op, and this current op s an optimized away rv2cv
             # XXX is ->gv()->sv() the way to get at the value in <5>gv(*FooBar::foo)? seems to work
             # XXX can we safely assume $lastpack if we can't find :: in the name?
             # debug - confess
             ($type, $method) = $op->first()->gv()->sv() =~ m{^\*(.*)::([^:]+)$} or confess;  
             $debug and print "debug: ", __LINE__, ": we think we have a function call - package $type function $method\n";
             return if $method eq 'proto'; # XXX
             $success = 1;
             return 1;
           }
           $argop ||= $op;
           $op = $op->sibling();
         }
         return;
       },
     ) {
       $debug and print "debug: ", __LINE__, ": foo() - normal function call: considering: ", $op->name(), "\n";
       last unless $test->(); 
       $op = $op->sibling() or last;
     }

     return check_args($argop, $type, $method) if $success;

  }

  # $a->bar();

  # this one is tricky. we have to get $a's type to get bar's package to see if that matches $b's type.

  # k        <1> entersub[t4] sKS/TARG ->l       <--- this node is the one given to us
  # c           <0> pushmark s ->d
  # d           <0> padsv[$a:3,5] sM ->e         .... may not be a padsv - should use solve_type()! XXX
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
         while($op and $op->name() ne 'method_named') {
           $argop ||= $op;
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
                  " in expression that should return " . $expected->diagnostics() . nastily if $expected;
       } else {
         my $type = lookup_targ($targ)->type() or die nastily;          # $a, from "$b = $a->bar()"
         lookup_method($type) or die 'unknown package: ' . $type . ' ' . nastily;
         return check_args($argop, $type, $method);
       }

     }

  }

  # sassign
  # aassign
  # binops that target pads

  if($self->name() eq 'sassign' or
     $self->name() eq 'aassign' or
     (ref($self) eq 'B::BINOP' and $self->private() & OPpTARGET_MY)
  ) {{

    $debug and print 'debug: ', __LINE__, ": considering ", $self->name(), " at line $lastline\n";

    # the left hand side is what is being assigned to. if it isn't type-checked,
    # then type checking isn't in effect on this statement.
    # this refers to the side of the assign operator being applied to us.

    # in case of aassign (array assign, one list is assigned to another):
    # instead of calling solve_list_type() as might make sense, we instead just call
    # solve_type(), as either of the lists may have been optimized away, and solve_type()
    # handles this general case, kicking over to solve_list_type() as needed.

    # XXX - is the OPpTARGET_MY flag valid for all BINOPs?

    debug("sassign/aassign/binop-target-my: expected is true: ", $expected->diagnostics()) if $expected;

    my $left = solve_type($self->last(), $expected) or confess $self->last()->name(); 

    $debug and print 'debug: left diagnostics: ', $left->diagnostics(), 
                     ' opname: ', $self->last()->name(), ' ',
                     " at line $lastline.\n";

    my $right = solve_type($self->first(), $expected) or confess $self->first()->name();

    $debug and print 'debug: right diagnostics: ', $right->diagnostics(), 
                     ' opname: ', $self->first()->name(), ' ',
                     " at line $lastline.\n";

    $right->emit($expected) if $expected;
    $right->emit($left) if $left->type() ne 'none' and $left->type() ne 'unknown';

    $left->accept($right);

    # is something expected? make sure we get it!

    $right->isa($expected, 'value needed from assignment') if $expected;

    # special case - we don't know what the heck is on the left, but we know that the
    # value on the right will pass through in this one case.

    if($left->type() eq 'none' or $left->type() eq 'unknown') {
      # assignments tend to happen in void context, but might as well try and see if something should be returned
      return $right; 
    }

    # is the thing on the right a subtype of the variable meant to hold it?
    # our little type objects have their own isa() method.
    # XXX trying to get little packages wired up so that this works on primitive types as well as complex
    # XXX this isa test is redundant with accept() and emit() on arrays and possibly in the future, scalars

    $right->isa($left, 'unsafe assignment');
    return $left;

  }}

  #
  # listops
  # 

  if($self->name() eq 'lineseq' or
     $self->name() eq 'list' or
    (ref($self) eq 'B::LISTOP' and $self->first()->name() eq 'pushmark')       # stolen from types.pm
  ) {

    # the lineseq stuff is redundant, but it serves to illustrate a common example.
    # general case - we have a list type, which is the GCD of all types in the list
    # a whole class of problems, really. an sassign is being done to the lvalue result of a list.
    # that lvalue result could be a type-checked variable used in a substr() or other lvalue
    # built in, or it could be a declaration being assigned to right off, perhaps from a 
    # constructor. 
    # solve_types() should be able to go into a list and figure out which type checked scalar (if any)
    # is the fall through value - XXX. in order to do this, we'd have to track what arguments go into and
    # come out of each op, and then when the block ends, remember which op was the last. 
    # XXX okey, i'm pretty fuzzy on all of this here
    # return, above, we don't check the result type, but we propogate the expected type. 
    # here, we propogate the expected type and we check the common result type. 

    my $return = solve_list_type($self->first(), $expected);
    $debug && $expected and print "debug: ", __LINE__, ": expecting ", $expected->diagnostics(), "\n";
    return $return unless $expected;
    # $return->isa($expected); # XXX this is a no-op
    # check_types($return, $expected, 0); # XXX should be 1 - fatal if mismatch
    return $return;

  }

  #
  # nothing we recognize. we're going to return "unknown", but first we should make sure
  # that expressions nested under this point get inspected for type safety. so, we 
  # recurse, expecting nothing.
  # 

  if($self->flags() & OPf_KIDS) {
    # this should work for unops, binops, *and* listops

    $debug and print "debug: ", __LINE__, ": generic handling for UNOP/BINOP/LISTOPs: handling op: ", $self->name(), "\n";

    # my $lasttype;
    # this was how it was done:
    # for(my $kid = $self->first(); $$kid; $kid = $kid->sibling()) {
    #   # solve_type($kid, $expected); # too much to ask without understanding the ops themselves
    #   # however, we could probably return the type of the last, if any
    #   $lasttype = solve_type($kid, undef);
    # }
    # $debug && $expected and print "debug: ", __LINE__, ": recursing through unknown op, we pass through type ", 
    #                               $lasttype->diagnostics(), " - we were expecting " . $expected->diagnostics() . "\n";
    # $lasttype->isa($expected, 'expression was expected to evaluate to a certain type') if $expected;
    # return $lasttype if $lasttype->type() ne 'none';

    # this is how it is being done now - experimental:
    # solve_list_type() looks at returns, and if anywhere should try to figure out where the fall-through value is, it is there.
    # solve_list_type($self->first(), $expected);
    # return solve_list_type($self->first(), undef);

    return enforce_list_type($self->first(), $expected);

  }

  $debug and print "debug: ", __LINE__, ": unknown op: ", $self->name(), " context: $want\n";

  return canned_type('unknown')->clone(sprintf 'unrecognized scalar construct (op: %s)', $self->name()) if($want == OPf_WANT_SCALAR);
  return canned_type('unknown')->clone(sprintf 'unrecognized list construct (op: %s)', $self->name())   if($want == OPf_WANT_LIST);
  return canned_type('none')->clone(sprintf 'unrecognized void construct (op: %s)', $self->name())      if($want == OPf_WANT_VOID);

  $debug and print "debug: ", __LINE__, ": unknown context number $want - that sucks\n";
  return canned_type('none')->clone(sprintf 'unrecognized construct in unrecognized context (op: %s)', $self->name());

}

#
# check method call arguments against prototype
#

sub check_args {

  # someone somewhere found something that looks like a method call.
  # we check the arguments to that method call against the methods prototype.
  # we also make sure that that method has a prototype, is a constructor, or else the
  # method appears in the package via can(), since we don't want to compute inheritance manually.
  # XXX if we can track down the package where it is defined, we might find a prototype there.
  # we die if the prototype doesn't match the actual types of the chain of ops.
  # in case of a match, we return the typeob representing the prototype of this function.

  my $op = shift;
  my $type = shift;
  my $method = shift;

  # no $op means no arguments were found. this might be what the prototype is looking for! is this safe? XXX

  # $debug && ! $op and print "debug: ", __LINE__, " check_args called without an OP! type: $type method: $method\n";
  # $debug && $op and print "debug: ", __LINE__, ": check_args called: op: ", $op->name(), ' ', $op->seq(), 
  #                         " type: $type method: $method\n";

  my $argob;

  # default case - method is prototyped in the package specified by type
  $argob = lookup_method($type, $method) if lookup_method($type, $method);

  # if method is 'new' and no type exists, default to the type of the reference
  if($method eq 'new' and ! $argob) {
    $argob = typesafety::methodob->new(type=>$type, package=>$type, name=>'new', desc=>'constructor');
  }

  # kludge, but inheritance doesn't work otherwise!
  if(! $argob and $type->can($method)) {
    $argob = typesafety::methodob->new(type=>$type, package=>$type, name=>$method, desc=>'inherited/unprototyped method');
  }

  $argob or die "unknown method. methods called on type safe objects " .
                 "must be prototyped with proto(). package: " . $type . ' method: ' . $method . ' ' . nastily;

  # at this point, we know the return type of the method call. now, we check the argument signiture, if there is one.
  # if we cooked up our own because new() wasn't prototyped, then there won't be one. that's okey.

  my $takes = $argob->takes();

  unless($takes and @$takes) {
    # this method's arguments aren't prototyped
    # success, so far. this is this being assigned to something else, that might conflict if we also don't have
    # any type information.
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
  my $rightob;

  # XXX we hardcode in method_named - really, we just want to discard the last op in the stream.
  # XXX otherwise, this will prevent checking function prototypes.

  while($leftop and $leftop->name() ne 'method_named') {

    if(! exists $takes->[$index]) {
      die "more parameters passed than specified in prototype. calling $method in $type, " . nastily;
    }

    # $debug and print "debug: ", __LINE__, ": checking prototype: considering: ", $leftop->name(), "\n";

    $left = $takes->[$index];
    goto OKEY if ! $left;

    $rightob = solve_type($leftop); 

    if($left and ! $rightob) {
      confess "argument number " . ($index + 1) . " must be type $left according to prototype. " . 
           'instead, it is a(n) ' . $rightob->diagnostics() . nastily;
    }

    # rightob->isa(left)

    goto OKEY if $rightob->type() eq $left;
    goto OKEY if $rightob->type()->isa($left); # $left is a plain string here, so we have to do ->type()
    die "argument number " . ($index + 1) . " type mismatch: must be type '$left', instead we got a(n) " .
        $rightob->type() . ' ' . nastily; 

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
# solve types of lists
#

sub solve_list_type {

    # a 'list' op was found - any number of things could be littered onto the stack.
    # this calculates the largest common type of those objects, if any. yes, this means
    # arrays can't contain mixed information - they're an array of one base kind of object
    # or integers or floats or something. 
    # the first sibling under list is passed in.
    # this is called from solve_type(), and itself calls solve_type().
    # stolen from types.pm by Auther Bergman, then hacked into worthlessness
    # this can be used any place where solve_type() may be used - a list of one op is just fine.

    my $op = shift;
    my $expected = shift;

    my @types;
    my $type;

    while($$op) {
        # $debug and print "debug: ", __LINE__, ": trying to solve type for op ", $op->name(), ' ', $op->seq(), "\n";
        # confess "solve_type for " . $op->name() . " did it - ref type " . ref $types[-1] unless ref($types[-1]) and $types[-1]->isa('typesafety::typeob'); # debug # heh - our new ->isa() broke this
        # this is a bit different now - we only consider the return if the op actually puts something onto the stack - no more voids!

        $type = solve_type($op, $expected);
        confess "offending op was " . $op->name() . ' returned to us: ' . $type unless ref($type) and UNIVERSAL::isa($type, 'typesafety::typeob');
        push @types, $type if $type->type() ne 'none';
        $op = $op->sibling();

    }

    $debug and print "debug: ", __LINE__, ": okey, this is what solve_list_type() has to work with: ", join ', ', map({ $_->type() } @types), "\n";

    my $encapsulates = common_type_from_list(@types);

    $debug and print "debug: ", __LINE__, ": aren't we clever? greatest common type: ", $encapsulates->diagnostics(), "\n";

    return $encapsulates;

}

sub common_type_from_list {

    # which object, if any, encapsulates all of the others?
    # if there are several, they must all be the same class, right?
    # if there are none, there is no common type to this list!

    my @types = @_;

    OUTTER: 
    foreach my $outter (@types) {

      foreach my $inner (@types) {
        next if $inner->type() eq 'none';
        next OUTTER if $outter->type() eq 'none';
        next OUTTER unless $outter->isa($inner);
      }

      return $outter;
      # push @encapsulates, $outter;

    }

    # build up a super-none from all of the types - no common type can be found.
    return canned_type('none')->clone('no common type in list:' . join ', ', map { $_->diagnostics() } @types);

}


sub uncommon_type_from_list {

    # which object, if any, is not encapsulated by any other? opposite of common_type_from_list()

    my @types = @_;

    OUTTER: 
    foreach my $outter (@types) {
      next if $outter->type() eq 'none';

      foreach my $inner (@types) {
        next if $inner->type() eq 'none';
        next OUTTER if $inner->isa($outter);
      }

      return $outter;

    }

    return $types[0]; # all the same thing, doesn't matter
}

sub solve_lit {

  # an op returns a litteral string that is used as a type name - currently only used by 'bless' in solve_type()

  my $self = shift;

  if($self->name() eq 'const') {
    return $self->sv()->sv();
  }

  if($self->name() eq 'ref') {{
    last unless $self->first()->name() eq 'padsv';
    my $typeob = lookup_targ($self->first()->targ());
    last unless $typeob;
    return $typeob->type();
  }}

  # print $_[0];

  # 6  <@> leave[t1] vKP/REFC ->(end)
  # 1     <0> enter ->2
  # 2     <;> nextstate(main 1 -e:1) v ->3
  # 5     <@> print vK ->6
  # 3        <0> pushmark s ->4
  # -        <1> ex-aelem sK/2 ->5
  # -           <1> ex-rv2av sKR/1 ->-
  # 4              <$> aelemfast(*_) s ->5
  # -           <0> ex-const s ->-

  if($self->name() eq 'aelemfast') {{
    # index is in ->private(), the array itself in ->sv(). how so very CISC. 
    # debug("aelemfast: gv stash name: ", $self->gv()->STASH()->NAME()   );  # main
    # we're ignoring typeob->aelem_prototype() for now and naively assuming the 0th argument to be the package type
    # $lastpack is almost correct - in some cases a subclass that inherits the constructor will be the actual type
    # returned at runtime, but considering the base type is safe from an analysis standpoint.
    last unless $self->gv()->NAME() eq '_'; # better known as the default argument list, @_
    last unless $self->private() == 0;
    return $lastpack; 
  }}

}

#
# utility methods
#

# these just factor out some of the cruftier syntax

sub enforce_type {
  # common repeated code sequence - 
  # solve a type; if a type is expected, make sure it is that type
  my $op = shift;
  my $expected = shift;
  my $reason = shift;
  my $type = solve_type($op, $expected);
  $type->isa($expected, $reason || 'type mismatch - ') if $expected;
  return $type;
}

sub enforce_list_type {
  # common repeated code sequence - 
  # solve a type; if a type is expected, make sure it is that type
  my $op = shift;
  my $expected = shift;
  my $reason = shift;
  my $type = solve_list_type($op, $expected);
  $type->isa($expected, $reason || 'type mismatch - ') if $expected;
  return $type;
}

sub lexicalname {
  # given a pad number (stored in all perl operators as $op->targ()), return its name.
  # works well - we get "$foo" etc back
  # PVX() returns the string stored in a scalar as null terminated, ignoring the length info, 
  # which is the correct thing to do with pad entries (length info is barrowed for something else).
  # otherwise, PVX() is like PV().
  my $targ = shift;
  my $padname = (($curcv->PADLIST->ARRAY)[0]->ARRAY)[$targ];  # from B::Concise
  return 'SPECIAL' if B::class($padname) eq 'SPECIAL';
  return $padname->PVX(); 
}

sub lexicalref {
  # given a pad number, return a B object representing it as a scalar.
  # pads are stored as a parallel array of names/metainformation and actual scalar references to the data.
  my $targ = shift;
  (($curcv->PADLIST->ARRAY)[1]->ARRAY)[$targ]->sv(); 
}

sub pppname {
   # like ppname, but we take the op itself. saves typing. returns something like "pp_list".
   my $self = shift;
   return $self->can('targ') ? ppname($self->targ()) : 'null';
}

sub denull {

  my $op = shift;

  if(
     $op->name() eq 'null' and 
     $op->can('targ') and 
     # ppname($op->targ()) eq 'pp_list' and
     $op->flags() & OPf_KIDS and
     $op->can('first')
   ) {
     debug('denull descending past null op ', ppname($op->targ()), ' to: ', $op->first()->name());
     $op = $op->first();
     return denull($op);
   }


   return $op;

}

sub source_status { return ($lastpack, $lastfile, $lastline) }


#
# typeob
#

# represents a type itself, including where it was defined, how it was defined, and how it is actually used.
# type data associated with a typed scalar - includes verbose information about where the type was defined
# for good diagnostics in case of error

package typesafety::typeob;

# accessors

sub type     :lvalue { $_[0]->[0] }  # point of our existance
sub package  :lvalue { $_[0]->[1] }  # diagnostic output in case of type match failure
sub filename :lvalue { $_[0]->[2] }  # diagnostics
sub line     :lvalue { $_[0]->[3] }  # diagnostics
sub pad      :lvalue { $_[0]->[4] }  # scalars only 
sub name     :lvalue { $_[0]->[5] }  # scalars only 
sub desc     :lvalue { $_[0]->[6] }  # scalar or method return? diagnostics? creating info?
sub takes    :lvalue { $_[0]->[7] }  # in the case of methods, what types (in order) do we take for args?

sub accepts          { $_[0]->[8] }  # arrayref of types of objects we've been asked to store
sub emits            { $_[0]->[9] }  # arrayref of types of objects we've been asked to provide
sub accept   { }                     # noop in this base class
sub emit     { }                     # noop in this bsae class

sub new { 
  my $self = bless ['none', typesafety::source_status(), (undef) x 4, [], []], shift(); 
  while(@_) { 
    my $f = shift; $self->$f = shift; 
  } 
  return $self; 
}

sub clone { 
  my $self = shift; 
  my @new = @$self; 
  # augment description - this is the primary (only?) change made to clones
  $new[6] ||= ''; $new[6] .= ' ' . $_[0] if @_;  
  typesafety::debug("new desc is $new[6]");
  # typesafety::cluck("new desc");
  bless \@new, ref $self;
}

sub diagnostics { 
  my $self = shift;
  sprintf "%s %s, type %s, defined in package %s, file %s, line %s", 
    map { $self->$_() || '?' } qw{desc name type package filename line};
}

sub isa {
  # wrapper for the normal UNIVERSAL::isa() test - should two typeobs not match, we die with diagnostics
  my $self = shift; 
  my $arewe = shift or typesafety::confess(); 
  ref $arewe or typesafety::confess(); 
  my $fatal = shift; 
  return 1 if $self->type() eq $arewe->type() or $self->type()->isa($arewe->type()); 
  return undef unless $fatal;
  die join ' ', $fatal, ($fatal?': ':''),  "type mismatch: expected: ", $arewe->diagnostics(), 
                "; got: ", $self->diagnostics(), typesafety::nastily(); 
}

package typesafety::scalarob; 

use base 'typesafety::typeob'; 

sub typesafety::scalarob::stuff { 'scalar' }

#
# typesafety::methodob
#

package typesafety::methodob; 

use base 'typesafety::typeob'; 

sub typesafety::methodob::stuff { 'method' }

sub argnum    :lvalue { $_[0]->[10] }   # next argument position to be read 

sub unshift_prototype {
  my $self = shift;
  my $takes = $self->takes; 
  my $argnum = $self->argnumb++;
  return $self->type() if $argnum == 0;   # OO perl adds $self as first argument
  return $takes->[$argnum - 1];
}

sub aelem_prototype {
  my $self = shift;
  my $argnum = shift;
  my $takes = $self->takes; 
  return $self->type() if $argnum == 0;   # OO perl adds $self as first argument
  return $takes->[$argnum - 1];
}

sub reset_prototype { $_[0]->argnum = 0; }

#
# typesafety::arrayob
#

package typesafety::arrayob;  

use base 'typesafety::typeob'; 

sub stuff  { 'array' }

sub type :lvalue { 
  my $self = shift; 
  if((! $self->[0] or $self->[0] eq 'none') and @{$self->emits()}) {
     typesafety::debug("typesafety::arrayob::type computing array type from emits");
     $self->[0] = typesafety::common_type_from_list(@{$self->emits()})->type();
  }
  if((! $self->[0] or $self->[0] eq 'none') and @{$self->accepts()}) {
     typesafety::debug("typesafety::arrayob::type computing array type from accepts");
     $self->[0] = typesafety::uncommon_type_from_list(@{$self->accepts()})->type();
  }
  if(! $self->[0] or $self->[0] eq 'none') {
    typesafety::debug("typesafety::arrayob::type should be computing array type from emits but we have no emits or accepts yet");
  }
  $self->[0] ||= 'none'; 
  $self->[0]; 
}

sub accept   { my $self = shift; typesafety::debug("accept: ", $_[0]->diagnostics()); push @{$self->accepts()}, shift(); $self->compat(); $self; } # things on the lhs accept
sub emit     { my $self = shift; typesafety::debug("emit: ", $_[0]->diagnostics()); push @{$self->emits()}, shift(); $self->compat(); $self; }   # things on the rhs emit

sub compat { 
  my $self = shift; 
  my @left = @{$self->accepts()} or return;
  my @right = @{$self->emits()} or return;
  typesafety::debug('compat: getting ready to permute');
  foreach my $right (@right) { 
    foreach my $left (@left) { 
      # this is backwards from normal, but so is our role - normally, we test if data can be downgraded to fit its container. here, we want to
      # test to make sure that we haven't downgraded beyond what is acceptable.
      typesafety::debug("compat: permuting: left: ", $left->diagnostics(), " = right: ", $right->diagnostics(), "\n");
      $left->isa($right, 'array used inconsistently'); 
    } 
  } 
  typesafety::debug('compat: end permute');
}

#
# other other diddling around in other packages
#

# none, constant, int, float, string

@none::ISA = ();
push @int::ISA, 'none';
push @float::ISA, 'int';

sub B::NULL::name { 'null' }

1;

=pod

=head1 NAME

typesafety.pm - compile-time type usage static analysis 

=head1 SYNOPSIS

  package main;
  use typesafety; # 'summary', 'debug';

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
    bless [], $_[0]; # or bless whatever, __PACKAGE__ or bless whatever, 'FooBar'
  }

  sub foo { my $me = shift; return $me->new(); } 

  #

  package BazQux;
  use typesafety;
  @ISA = 'FooBar';

=head1 DESCRIPTION

  This is a SNAPSHOT release of ALPHA software. This is the third snapshot.
  The first was ugly, ugly, ugly and contained horrific bugs and the implementation
  was lacking. The second continued to lack numerous critical features.
  Much remains to be done and much is in progress. The interface is
  in flux. See BUGS, below.

Hueristics similiar to "taint.pm" track dataflow.

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

A few specific things are inspected in the program when 
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

  bless something, $_[0];
  bless something, __PACKAGE__;
  bless something, 'FooBar';

This is considered to return an object of the type of the hard-coded value
or of the present package. This value may "fall through" and be the default
return value of the function.

  return $whatever;

Return values in methods must match the return type prototyped for that
method.

  push @a, $type;
  unshift @a, $type;
  $type = pop @a;
  $type = shift @a;
  $type = $a[5];

When typed variables and typed expressions are used in conjunction with arrays, the
array takes on the types of all of the input values. Arrays only take on 
types when assigned from another array, a value is C<push>ed onto it, or a
value is C<unshift>ed onto it.
Whenever the array is used to generate a value with an index, via C<pop>,
or via C<unshift>, the expected type is compared to each of the types the
array holds values from. Should a value be assigned to the array that
is incompatiable with the types expected of the array, the program dies
with a diagnostic message.
This feature is extremely experimental. In theory, this type of automatic type
inference could be applied to method arguments, scalars, and so forth, such that
types can be specified by the programmer when desired, but never need to be, and
the program is still fully type checked. O'Caml reported does this, but with a 
concept of records like datastructures, where different elements of an array
are typed seperately if the array isn't used as a queue. We only support
one type for the whole array, as if it were a queue of sorts.

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

Blesses are only recognized as returning a given type when not used with a variable,
or when used with C<< $_[0] >>.
E.g., all of these are recognized: C<< bless {}, 'FooBar' >>, 
C<< bless {}, $_[0] >>, and
C<< bless {}, __PACKAGE__ >>. (C<< __PACKAGE__ >> is a litteral as far as perl is concerned). 
Doing C<< bless {}, $type >> and other constructs will throw a diagnostic about
an unrecognized construct - C<typesafety.pm> loses track of the significance of
C<$_[0]> when it is assigned to another variable. 
To get this going, I'd have to track data as it is unshifted
from arguments into other things, and I'd have to recognize the result of C<ref>
or the first argument to new as a special thing that produces a predictable type
when feed to C<new> as the second argument. Meaty.

C<undef> isn't accepted in place of an object. Most OO langauges permit this - 
however, it is a well known duality that leads to checking each return value.
This is a nasty case of explicit type case analysis syndrome. Rather than
each return value be checked for nullness (or undefness, in the case of Perl)
and the error handling logic be repeated each place where a return value
is expected, use the introduce null object pattern: return values should
always be the indicated type - however, a special subclass of that type
can throw an error when any of its methods are accessed. Should a method
call be performed to a method that promises it will always return a given
type, and this return value isn't really needed, and failure is acceptable,
the return can be compared to the special null object of that class.
The normal situation, where a success return is expected, is handled
correctly without having to introduce any ugly return checking code or
diagnostics. The error reporting code is refactored into the special
null object, rather than be littered around the program, in other words.

Incoming data is checked against the prototype, but it doesn't take on the
given type inside of the method. A FooBar isn't usable as a FooBar when it is
an argument. This sucks pretty bad. I B<almost> have this working - the
infastructure is there. I just need to add some more heuristics to look
for these cases. This is the primary thing preventing this module from
being usable.

We're intimately tied to the bytecode tree,
the structure of which could easily change in future versions of Perl. This
works on my 5.9.0 pre-alpha. It might not work at all on what you have.

Only operations on lexical C<my> variables are supported. Attempting to
assign a global to a typed variable will be ignored - type errors
won't be reported. Global variables themselves cannot yet be type checked.
All doable, just ran out of steam.

Only operations on methods using the C<< $ob->method(args) >> syntax is 
supported - function calls are not prototyped nor recognized. Stick
to method calls for now. New - function prototypes might work, but 
I haven't tested this, nor written a test case.

Types should be considered to match if the last part matches - C<< Foo::Bar->isa('Bar') >> would be true.
This might take some doing. Workaround to C<::> not being allowed in attribute-prototypes.
Presently, programs with nested classes, like C<Foo::Bar>, cannot have these types assigned
to variables. No longer true - the C<declare()> syntax is a work-around to this.

Many valid, safe expressions will stump this thing. It doesn't yet understand all
operations - only a small chunk of them. C<map { }>, when the last thing in the
block is type safe, C<grep { }>, slice operations on arrays, and dozens of other
things could be treated as safe. When C<typesafety.pm> encounters something it doesn't
understand, it barfs.

We use B::Generate just for the C<< ->sv() >> method. Nothing else. I promise! We're not modifying
the byte code tree, just reporting on it. I B<do> have some ideas for using B::Generate,
but don't go off thinking that this module does radical run time self modifying code stuff.

The root (code not in functions) of C<main::> is checked, but not the roots of other modules.
I don't know how to get a handle on them. Sorry. Methods and functions in C<main::> and other
namespaces that C<use typesafety;> get checked, of course.

Having to call a "check" function is kind of a kludge. I think this could be done in a
C<CHECK { }> block, but right now, the C<typesafety::check()> call may be commented out,
and the code should start up very quickly, only having to compile the few thousand
lines of code in C<typesafety.pm>, and not having to actually recurse through the 
bytecode.
Modules we use have a chance to run at the root level, which lets the C<proto()> functions
all run, if we are used after they are, but the main package has no such benefit. Running
at CHECK time doesn't let anything run. 

The B tree matching, navigation, and type solving logic should be presented as a 
reusable API, and a module specific to this task should use that module. After I 
learn what the pattern is and fascilities are really needed, I'll consider this. 

Tests aren't run automatically - I really need to fix this. I keep running them
by hand. It is one big file where each commented-out line gets uncommented
one by one. This makes normal testing procedures awkward. I'll have to rig something up.

Some things just plain might not work as described. Let me know.

=head1 SEE ALSO

L<types>, by Arthur Bergman - C style type checking on strings, integers,
and floats. 

L<http://perldesignpatterns.com/?TypeSafety> - look for updated documentation
on this module here - this included documentation is sparse - only usage
information, bugs, and such are included. The TypeSafety page on 
L<http://perldesignpatterns.com>, on the other hand, is an introduction and
tutorial to the ideas.

L<http://www.c2.com/cgi/wiki?NoseJobRefactoring> - an extreme case of the
utility of strong types.

L<Class::Contract>, by Damian Conway

L<Attribute::Types>, by Damian Conway

L<Sub::Parameters>, by Richard Clamp

L<Object::PerlDesignPatterns>, by myself. 

The realtest.pl file that comes with this distribution demonstrates exhaustively
everything that is allowed and everything that is not. 

The source code. At the top of the .pm file is a list of outstanding issues,
things that I want to do in the future, and things that have been knocked down.
At the bottom of the .pm file is a whole bunch of comments, documentation, and
such.

L<http://perldesignpatterns.com/?PerlAssembly> - C<typesafety.pm> works by
examining the bytecode tree of the compiled program. This bytecode is known
as "B", for whatever reason. I'm learning it as I write this, and as I
write this, I'm documenting it (talk about multitasking!)
The PerlAssembly page has links to other resources I've found around the
net, too.

=head1 AUTHOR

Scott Walters - scott@slowass.net

=head1 COPYRIGHT

Distribute under the same terms as Perl itself.
Copyright 2003 Scott Walters. Some rights reserved.

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
    return get__ob(lookup_targ($targ), 'okey') if lookup_targ($targ);
    print "debug: list/padsv: undef - targ: $targ name: ", lexicalname($targ), "\n" if $debug;
    get__ob(undef, "non-type-checked scalar: '" . lexicalname($targ) . '"');
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

---------

    my $cv = $op->find_cv();

            $typed{$cv->ROOT->seq}->{$op->targ}->{type} = $target->SvSTASH->NAME;
            $typed{$cv->ROOT->seq}->{$op->targ}->{name} = $target->PV;

--------

package FooBar; package main; my FooBar @foos;

Can't declare class for non-scalar @foos in "my" at -e line 1, near "my FooBar @foos"
Execution of -e aborted due to compilation errors.

# we don't like typechecked arrays. blurgh.

-------------

lightbright# perl -MO=Concise -e 'my $a = sub { print @_, "\n"; }; $a->(1, 2, 3, 4);'
g  <@> leave[$a:2,3] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 2 -e:1) v ->3
7     <2> sassign vKS/2 ->8
5        <1> refgen sK/1 ->6
-           <1> ex-list lKRM ->5
3              <0> pushmark sRM ->4
4              <$> anoncode[CV ] lRM ->5
6        <0> padsv[$a:2,3] sRM*/LVINTRO ->7
8     <;> nextstate(main 3 -e:1) v ->9
f     <1> entersub[t3] vKS/TARG,1 ->g
-        <1> ex-list K ->f
9           <0> pushmark s ->a
a           <$> const(IV 1) sM ->b
b           <$> const(IV 2) sM ->c
c           <$> const(IV 3) sM ->d
d           <$> const(IV 4) sM ->e
-           <1> ex-rv2cv K/1 ->-
e              <0> padsv[$a:2,3] s ->f

# entersub is an interesting beast. so far, we've seen the last thing in the list be 
# method_named('new'), ex-rv2cv->gv(*FooBar::foo), ex-rv2cv-> refgen-> ex-list-> pushmark-> anoncode,
# and now ex-rv2cv->padsv($coderef).
# the last argument may be any expression that results in a valid coderef. neato!
# we need a generic mechanism for tracking down a prototype given this last argument and the first argument.
# even without a prototype, we should be able to get a return value.

---------------

Disturbing:

my $a = <>; 

-     <1> null vKS/2 ->6
3        <0> padsv[$a:1,6] sRM*/LVINTRO ->4
5        <1> readline[t2] sKS/1 ->6
4           <$> gv(*ARGV) s ->5

This looks like it should be an sassign. It isn't. It is a padsv followed by readline with the OPf_STACKED bit set.
Normally, we'd expect something like this:

   sassign
     padsv
     readline
       gv

To grok this, we'd have to count the pushmarks and ops that leave things on the stack (which we don't know how
to deturmine, and I doubt it is even possible! some ops leave things sometimes but not others, i think).
Then when we see something OPf_STACKED, we must see what is on top of this stack - most recently added.
Fugly.

Oh, things marked OPf_REFERECE (reference, will modify, valid as lvalue) are things likely to be assigned
to in this case, where something like a const may be used but won't be a target.

---------------

if($a) { print "hi\n"; } elsif(defined $a) { print "yes" } else { print "bye" }

-     <1> null vKP/1 ->c
8        <|> cond_expr(other->9) vK/1 ->d                <-- if
7           <0> padsv[$a:1,6] s ->8                      <-- ($a)
-           <@> scope vK ->-                             <-- { print "hi\n" }
-              <0> ex-nextstate v ->9
b              <@> print vK ->c
9                 <0> pushmark s ->a
a                 <$> const(PV "hi\n") s ->b
-           <1> null vK/1 ->-                            <-- else *or* elsif clauses hung off of 3rd arg to cond_expr
f              <|> cond_expr(other->g) vK/1 ->j          <-- hey, just like another if! these just keep nesting deeping and deeper each elsif
e                 <1> defined sK/1 ->f
d                    <0> padsv[$a:1,6] s ->e
-                 <@> scope vK ->-
-                    <0> ex-nextstate v ->g
i                    <@> print vK ->c
g                       <0> pushmark s ->h
h                       <$> const(PV "yes") s ->i
o                 <@> leave vKP ->c
j                    <0> enter v ->k
k                    <;> nextstate(main 4 -e:1) v ->l
n                    <@> print vK ->o
l                       <0> pushmark s ->m
m                       <$> const(PV "bye") s ->n

for(my $i = 1..20) { print $i, "\n"; }

k  <@> leave[$i:1,3] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 3 -e:1) v ->3
j     <2> leaveloop vK/2 ->k
a        <{> enteriter(next->g last->j redo->b) lK ->h
-           <0> ex-pushmark s ->3
-           <1> ex-list lKM ->9
3              <0> pushmark sM ->4
8              <2> sassign sKMS/2 ->9
-                 <1> null sK/1 ->7
6                    <1> flop sK/LINENUM ->7
m                       <1> flip[t3] sK/LINENUM ->7
4                          <|> range(other->5)[t2] sK/1 ->l
l                             <$> const(IV 1) s ->m
5                             <$> const(IV 20) s ->6
7                 <0> padsv[$i:1,3] sRM*/LVINTRO ->8
9           <$> gv(*_) s ->a
-        <1> null vK/1 ->j
i           <|> and(other->b) vK/1 ->j
h              <0> iter s ->i
-              <@> lineseq vK ->-
b                 <;> nextstate(main 2 -e:1) v ->c
f                 <@> print vK ->g
c                    <0> pushmark s ->d
d                    <0> padsv[$i:1,3] l ->e
e                    <$> const(PV "\n") s ->f
g                 <0> unstack v ->h


--------------

Context - void vs scalar:

# print my $a=10, "\n";

9  <@> leave[$a:1,2] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 1 -e:1) v ->3
8     <@> print vK ->9
3        <0> pushmark s ->4
6        <2> sassign sKS/2 ->7
4           <$> const(IV 10) s ->5
5           <0> padsv[$a:1,2] sRM*/LVINTRO ->6
7        <$> const(PV "\n") s ->8

# my $a=10;

6  <@> leave[$a:1,2] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 1 -e:1) v ->3
5     <2> sassign vKS/2 ->6
3        <$> const(IV 10) s ->4
4        <0> padsv[$a:1,2] sRM*/LVINTRO ->5

Look at the padsvs - when the my appears in a print, it is in
scalar context. When it appears off of root, it is in void context.

#           v      OPf_WANT_VOID    Want nothing (void context)
#           s      OPf_WANT_SCALAR  Want single value (scalar context)
#           l      OPf_WANT_LIST    Want list of any length (list context)

# currently the real problem is $expected propogating where it shouldn't - we need two levels of $expected -
# one for "this expression MUST evaluate to" and another for "anything returned out of this code block must be".
# the first implies the latter. either all of that, or else we need to be able to tell when an expression doesn't
# return anything and ignore its (lack of) output. which it looks like we might be able to acheive!
# possible solutions: 
# x. info from opcodes.pl about whether each arg is a list, scalar, array, etc. somewhat useful, maybe.
# x. hand crafted list of which ops sometimes return things and those that never do. if we get to the
#    bottom and haven't found anything yet, then we can return the "none" typeob.
# x. context!

-----------------------

       Scratchpads and recursion

       In fact it is not 100% true that a compiled unit contains
       a pointer to the scratchpad AV. In fact it contains a
       pointer to an AV of (initially) one element, and this ele-
       ment is the scratchpad AV. Why do we need an extra level
       of indirection?

       The answer is recursion, and maybe threads. Both these can
       create several execution pointers going into the same sub-
       routine. For the subroutine-child not write over the tem-
       poraries for the subroutine-parent (lifespan of which cov-
       ers the call to the child), the parent and the child
       should have different scratchpads. (And the lexicals
       should be separate anyway!)

       So each subroutine is born with an array of scratchpads
       (of length 1).  On each entry to the subroutine it is
       checked that the current depth of the recursion is not
       more than the length of this array, and if it is, new
       scratchpad is created and pushed into the array.
       The targets on this scratchpad are "undef"s, but they are
       already marked with correct flags.

        my $target = (($cv->PADLIST->ARRAY)[1]->ARRAY)[$op->padix];
        my $name =   (($cv->PADLIST->ARRAY)[0]->ARRAY)[$targ];  # from B::Concise


---------

Context propogation:

       When a context for a part of compile tree is known, it is
       propagated down through the tree.  At this time the con-
       text can have 5 values (instead of 2 for runtime context):
       void, boolean, scalar, list, and lvalue.  In contrast with
       the pass 1 this pass is processed from top to bottom: a
       node's context determines the context for its children.

------

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

---------

Two constructs that *must* be supported in methods in order for this whole thing to be useful:

my $foo = shift 

8  <@> leave[$foo:1,2] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 1 -e:1) v ->3
7     <2> sassign vKS/2 ->8
5        <1> shift sK/1 ->6
4           <1> rv2av[t2] sKRM/1 ->5           <-- below here will be different in a method - *_ instead of *ARGV
3              <$> gv(*ARGV) s ->4
6        <0> padsv[$foo:1,2] sRM*/LVINTRO ->7

my($a, $b, $c) = @_ 

b  <@> leave[$a:1,2] vKP/REFC ->(end)
1     <0> enter ->2
2     <;> nextstate(main 1 -e:1) v ->3
a     <2> aassign[t5] vKS ->b
-        <1> ex-list lK ->6
3           <0> pushmark s ->4
5           <1> rv2av[t4] lK/1 ->6           <-- below here will be different in a method - *_ instead of *ARGV
4              <$> gv(*_) s ->5
-        <1> ex-list lKPRM*/128 ->a
6           <0> pushmark sRM*/128 ->7
7           <0> padsv[$a:1,2] lRM*/LVINTRO ->8
8           <0> padsv[$b:1,2] lRM*/LVINTRO ->9
9           <0> padsv[$c:1,2] lRM*/LVINTRO ->a

-----------

    sub compat   { my $self = shift; my @in = @{$self->accepts()}; my @out = @{$self->emits()};
                   foreach my $out (@out) { foreach my $in (@in) { $in->isa($out, 'array used inconsistently'); } } }

Everything accepted into an array must by usable every place a value is expected from that array.
Lets say we have A, B, C, and D, such that D isa C, C isa B, and B isa A. So, the inheritance tree would
look like:

  A <- B <- C <- D

  arr->accept(C)    
  arr->accept(D)     
  arr->emit(B)   # no problem - C and D both pass the isa(B) test
  arr->accept(A) # problem - A does not pass the isa(B) test

As long is nothing is emitted, the array will accept anything. If one thing is emitted
from the array (pushed or shifted off), then everything added to that array at any point
must be an instance of that expected type. If multiple different types are expected at
different points, then everything added to the array must pass the isa test for each 
thing expected from it.

On a related note:

sub type in typesafety::typeob might want to consider doing something sort of like this:

  $self->[0] = common_type_from_list(@{$self->accepts()}) if ! $self->[0] and $self->accepts(); 

but get the least common type instead of most common, should the emits() test fail. This would cover cases
where where a value or two has been assigned to an array, and we want to know what to expect from it. Right
now, we're infering the type purely from has been assigned to it.

-------

<20>leavesub[$type:225,226]---lineseq-+-<1g>nextstate(BazQux 225 00.pl:42)
                                      |-<1l>sassign-+-<1j>shift---<1i>rv2av[t2]---<1h>gv(*_)
                                      |             `-<1k>padsv[$type:225,226]
                                      |-<1m>nextstate(BazQux 226 00.pl:42)
                                      |-null---<1p>and(other->1q)-+-<1o>ref[t4]---<1n>padsv[$type:225,226]
                                      |                           `-<1t>sassign-+-<1r>ref[t3]---<1q>padsv[$type:225,226]
                                      |                                         `-<1s>padsv[$type:225,226]
                                      |-<1u>nextstate(BazQux 226 00.pl:43)
                                      `-<1z>bless-+-ex-pushmark
                                                  |-<1x>srefgen---ex-list---<1w>anonlist---<1v>pushmark
                                                  `-<1y>padsv[$type:225,226]

debug: 666: recursing through unknown op, we pass through type unrecognized construct (op: rv2av) - we were expecting method new, type BazQux, defined in package BazQux, file realtest.pl, line 50
missing type information: got: unrecognized construct (op: rv2av); expected: method new, type BazQux, defined in package BazQux, file realtest.pl, line 50 in package BazQux, file realtest.pl, line 53 at typesafety.pm line 898.

Kind of makes me wonder why "shift" was a recognized construct. This construct is:

  my $type = shift; 
  $type = ref $type if ref $type;

Both of those lines should be grokked.

  bless { }, $type;

This should definately be grokked!

sub new {
  bless [], 'BazQux';
}

<1m>leavesub[t1]---lineseq-+-<1g>nextstate(BazQux 228 00.pl:44)
                           `-<1l>bless-+-ex-pushmark
                                       |-<1j>srefgen---ex-list---<1i>anonlist---<1h>pushmark
                                       `-<1k>const(PV "BazQux")


----------

