package typesafety;

# major outstanding issues - see Bugs in the POD

# o. should we clear $scalars between calls to different methods? i think Perl reuses the pad numbers, so yes.
# o. decypering lists for the padsv on the end still doesn't work. my FooBar $foo :typed = 1; happily runs.

# major resolved issues:

# v. $a->meth() - $methods{$scalars->{targ of $a}->type()}->{'meth'} should exist, period, or we're trying to
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
our $VERSION = '0.01';

use attributes;
use B;
use B::Generate;

# debugging

# $SIG{__DIE__} =  $SIG{INT} = sub {
#    # when someone does kill -INT <our pid> from the command line, dump our stack and exit
#    print STDERR shift, map { (caller($_))[0] ? sprintf("%s at line %d\n", (caller($_))[1,2]) : ''; } 0..30;
#    print STDERR join "\n", @_;
#    exit 1;
# };

# use attributes to flag the desired datatypes. then do simple static analisys, using the B backend.

my $methods;       # $methods->{$package}->{$sub} = ob
my $scalars;       # $scalars->{$targ} = ob
my %knownuniverse; # all known namespaces - our inspection list
my %args;          # use-type arguments
my $debug;         # debug mode

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
     $methods->{$caller}->{$method} = get_type_ob($type, $caller, $filename, $line, undef, $method, 'method', $takes);
     # print 'debug: ', $methods->{$caller}->{$method}->diagnostics(), "\n"; 
  };
  *{$caller.'::declare'} = sub :lvalue { 
    $_[1] 
  };
  return 1;
}

sub MODIFY_SCALAR_ATTRIBUTES {
  # this, like declare()'s definition above, does nothing when executed, but
  # generates signiture code in the bytecode tree. it is this signiture that
  # we recognize and extract information from.
  return () if $_[2] eq 'typed'; # success
  return undef;                  # don't know that attribute, sorry
}

sub get_type_ob {
  package typesafety::typeob;
  sub type     { $_[0]->[0] }  # our primary interest - do the types match?
  sub package  { $_[0]->[1] }  # diagnostic output in case of type match failure
  sub filename { $_[0]->[2] }  # diagnostics
  sub line     { $_[0]->[3] }  # diagnostics
  sub pad      { $_[0]->[4] }  # scalars only 
  sub name     { $_[0]->[5] }  # scalars only 
  sub desc     { $_[0]->[6] }  # scalar or method return?
  sub takes    { $_[0]->[7] }  # in the case of methods, what types (in order) do we take for args?
  sub diagnostics { sprintf "%s %s, type %s, defined in package %s, file %s, line %d", map { $_[0]->[$_] || '?' } (6, 5, 0, 1, 2, 3) }
  bless [@_], __PACKAGE__;
}

#
# verify that types are what the user specified
#

# this is the heart of this module.
# we grok the bytecode, looking for signiture pattern, and extract information
# from them. when a pattern is found, we update internal information, or
# else test internal information to see if something is "safe".

my $curcv; # codevalue to get pad entries from

sub check {

  # check the main area first - it may set things up that are in the scope of methods defined later
  $curcv = B::main_cv();
  B::walkoptree_slow(B::main_root(), 'typesafe', 0); 

  # each package that has used us, check them as well
  foreach my $package (keys %knownuniverse) {
    # print "knownuniverse: ", $package, "\n";
    foreach my $method (grep { defined &{$package.'::'.$_} } keys %{$package.'::'}) {
      summary();
      $scalars = {}; # blow away our concept of what pads are associated with what types as we switch pads
      next if $method eq 'proto';
      next if $method eq 'declare';
      # print "knownuiverse: method: $method\n";
      my $cv = *{$package.'::'.$method}{CODE};
      $curcv = B::svref_2object($cv);
      B::svref_2object($cv)->ROOT() or die;
      B::walkoptree_slow(B::svref_2object($cv)->ROOT(), 'typesafe', 0);
    }
  }

}

sub summary {
  if(exists $args{summary}) {
    # give a nice report of what we did
    print "typesafety.pm status report:\n";
    print "----------------------------\n";
    foreach my $typeob (values %$scalars) {
      print $typeob->diagnostics(), "\n";
    }
  }
}

my $lastline; my $lastfile; my $lastpack; my $lastvarname; 

sub nastily () { "$lastvarname in package $lastpack, file $lastfile, line $lastline"; }

sub B::OP::typesafe {

  my $self = shift; # op object

  my $sassign_okey = 0;

  # per-op callback. 
  # this is called once for each opcode in the program.
  # here, things get ugly. making sense of the perl bytecode tree takes some doing,
  # and there are several unrelated things we're looking for, making this bulky.
  # this is the way we read our B, read our B, read our B, so early in the mornin'!

  # print "debug: ", $self->name(), "\n";

  # 2     <;> nextstate(main 494 test.pl:32) v ->3

  if($self->name() eq 'nextstate') {

    # record where we are in the program - we use this information to relate bytecode
    # information with information recorded from attributes at compile time.

    $lastpack = $self->stash()->NAME();
    $lastfile = $self->file();
    $lastline = $self->line();

  }

  # declare FooBar => my $test3;

  # l  <;> nextstate(main 581 test.3.pl:25) v
  # m  <0> pushmark s
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

  #
  # actual type checks 
  #

  # $foo->foo(1, 2, 3);

  # 1d <;> nextstate(main 513 test.7.pl:29) v
  # 1e <0> pushmark s
  # 1f <0> padsv[$foo:511,513] sM
  # 1g <$> const(IV 1) sM
  # 1h <$> const(IV 2) sM
  # 1i <$> const(IV 3) sM
  # 1j <$> method_named(PVIV "foo") 
  # 1k <1> entersub[t8] vKS/TARG
  # 1l <;> nextstate(main 513 test.7.pl:33) v

  if($self->name() eq 'pushmark') {
    # don't allow method calls on typechecked objects unless that method is prototyped.
    # this is more than a little redundant with the $x=$y->z() below in solve_types(). XX
    my $op = $self->next();
    my $targ; 
    my $method;
    my $argop;
    # print "debug: method call check, line $lastline...\n";
    foreach my $test (
      sub { $op->name() eq 'padsv' and $targ = $op->targ()  },  
      sub { 
        while($op and $op->name() eq 'const') {
           $argop ||= $op;
           $op = $op->next() 
        }
        return if !$op or $op->name() ne 'method_named';
        $method = $op->sv()->sv();
      },
      sub { $op->name() eq 'entersub' },
    ) {
       # print "debug: considering: ", $op->name(), "\n";
       last unless $test->(); 
       $op = $op->next(); # using next() here, not sibling(), on purpose 
    }

    if(defined $targ and exists $scalars->{$targ} and defined $method) {
      # this lexical isn't type checked and we're not assigning the result. if $scalars->{$targ} doesn't exist, fine.
      my $type = $scalars->{$targ}->type() or die nastily;          # $a, from "$a->bar()"
      exists $methods->{$type} or die 'unknown package: ' . $type . ' ' . nastily;
      check_args($argop, $type, $method);
    }

  }

  if($self->name() eq 'sassign') {{

    # print "considering sassign at line $lastline\n";

    # the left hand side is what is being assigned to. if it isn't type-checked,
    # then type checking isn't in effect on this statement.
    # this refers to the side of the assign operator being applied to us.

    my $leftob = solve_type($self->last()); my $left = $leftob->typeob(); last unless $left;

    my $rightob = solve_type($self->first()); my $right = $rightob->typeob();

    $rightob->typeob() or die 'unsafe assignment: ' . $left->diagnostics() . ' cannot hold ' . $rightob->diagnostics() . ' ' . nastily;

    # print "debug: left type: ", $left->type(), " at line $lastline. right type: ", $right->type(), "\n";
    
    # do type match exactly? 

    last if $right->type() eq $left->type();

    # is the thing on the right a subtype of the variable meant to hold it?
    # this uses softrefs to call ->isa() on a string. the string represents the type.

    last if $right->type()->isa($left->type());

    # can't prove it to be safe. sorry.

    die 'unsafe assignment: ' . $left->diagnostics() . ' cannot hold ' .  $right->diagnostics() . ' ' . nastily;

  }}

}

sub associate_scalar {

    # found one of our scalar initialization constructs.
    # called from B::OP::typesafe.
    # we recognize the code, and we're going to try to recognize the line number and filename.
    # if we can do so, we have enough information to associate a type (and everything else in
    # a typeob) with a pad entry number.
    # yes, this is cheezy and dangerous. my first idea didn't work out.

    # this assumes that a unique pad slot exists for each variable. i haven't tested this
    # idea heavily. things might depend on other context information. i may have to come
    # back and fix this.

    my $pad = shift;   # pad slot number
    my $type = shift;  # litteral name of the type

    exists $scalars->{$pad} and 
      die lexicalname($pad) . ' already defined: first declaration: ' . $scalars->{$pad}->diagnostics() . ' ' . 
          ' second declaration: ' . nastily;

    $scalars->{$pad} = get_type_ob($type, $lastpack, $lastfile, $lastline, $pad, lexicalname($pad), 'variable');
    # print "debug: success - found pad of variable ", $scalars->{$pad}->name(), " - pad $pad, at file $lastfile line $lastline\n";
}

sub get_arg_ob {
  package typesafety::argob;
  sub typeob      { $_[0]->[0] }
  sub lastop      { $_[0]->[1] }
  sub diagnostics { $_[0]->[2] }
  bless [ @_ ], __PACKAGE__;
}

sub solve_type {

  # when an assignment is found, this is called for each of the right and left sides.
  # called from B::OP::typesafe and recursively by ourself.
  # solving argument types means finding the targ, which is the pad slot, and 
  # looking that up in $scalars, if possible. failure returns undef or just dies. 
  # returns typesafety::argob object representing the result and the where 
  # bytetree scanning left off.

  my $self = shift;

  if($self->name() eq 'const') {
    print "debug: const\n" if $debug;
    return get_arg_ob(undef, $self, "constant value: '" . $self->sv()->sv() . "'");
  }

  if($self->name() eq 'padsv') {
    # simple case
    print "debug: padsv\n" if $debug;
    # this happens when we see non-typesafe scalars, which we tolerate ;)
    # print "debug: no typeob entry for this pad! ", $self->targ(), ' ', 
    #   lexicalname($self->targ()), " line $lastline\n" unless exists $scalars->{$self->targ()};
    exists $scalars->{$self->targ()} or return 
      get_arg_ob(undef, $self, "non-type-checked scalar: '" . lexicalname($self->targ()) . '"');
    return get_arg_ob($scalars->{$self->targ()}, $self, "success");
  }

  # my $a = bar->new();

  # b     <2> sassign vKS/2 ->c
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

     print "debug: entersub (constructor?), line $lastline\n" if $debug;

     my $op = $self->first();
     my $type;
     my $success = 0;
     foreach my $test (
       sub { $op->name() eq 'pushmark' },
       sub { return unless $op->name() eq 'const'; $type = $op->sv()->sv(); return 1; },
       sub {
         while($op and $op->name() ne 'method_named') {
           # seek past method call arguments. in the future, we would type check those. XX.
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

  # $b = $a->bar();

  # this one is tricky. we have to get $a's type to get bar's package to see if that matches $b's type.

  # m     <2> sassign vKS/2 ->n
  # k        <1> entersub[t4] sKS/TARG ->l       <--- this node is the one given to us
  # c           <0> pushmark s ->d
  # d           <0> padsv[$a:3,5] sM ->e
  # e           <$> const(IV 5) sM ->f           <--- from here until we hit the method_named op,
  # f           <$> const(IV 4) sM ->g                we these are processed by arg_types() for type safety. 
  # g           <$> const(IV 3) sM ->h                the first argument gets held by $argop.
  # h           <$> const(IV 2) sM ->i
  # i           <$> const(IV 1) sM ->j
  # j           <$> method_named(PVIV "bar") s ->k
  # l        <0> padsv[$b:4,5] sRM* ->m

  if($self->name() eq 'entersub') {

     print "debug: entersub (method call on typed object)\n" if $debug;

     my $op = $self->first();
     my $method;   # bar, in "$b = $a->bar()"
     my $targ;     # $a, in "$b = $a->bar()", gets us this from its typeob
     my $success = 0;
     my $argop;    # pointer to opcode representing first argument

     foreach my $test (
       sub { $op->name() eq 'pushmark' },
       sub { return unless $op->name() eq 'padsv'; $targ = $op->targ(); return 1; }, 
       sub { 
         while($op and $op->name() ne 'method_named') {
           # seek past method call arguments. this is where we would check arguments types, too.
           $argop ||= $op;
           $op = $op->sibling();
         }
         return unless $op; 
         $method = $op->sv()->sv();                               # bar, in "$b = $a->bar()"
         $success = 1;
       },
     ) {
       # print "debug: considering: ", $op->name(), "\n";
       last unless $test->(); 
       $op = $op->sibling() or last;
     }

     if($success) {

       exists $scalars->{$targ} or die 'missing type information for ' . lexicalname($targ) . ' ' . nastily;
       my $type = $scalars->{$targ}->type() or die nastily;          # $a, from "$b = $a->bar()"
       exists $methods->{$type} or die 'unknown package: ' . $type . ' ' . nastily;

       return check_args($argop, $type, $method);

     }

  }

  # my FooBar $bar :typed = 1 and any number of other compound constructs

  # a whole class of problems, really. an sassign is being done to the lvalue result of a list.
  # that lvalue result could be a type-checked variable used in a substr() or other lvalue
  # built in, or it could be a declaration being assigned to right off, perhaps from a 
  # constructor. XXX
  # if we find an sassign, we oughtta just attempt to solve the left and right hand sides
  # of it in generic, seperate ways, rather than trying to fit each combination into
  # a seperate framework.

  # r     <2> sassign vKS/2 ->s
  # f        <$> const(IV 1) s ->g
  # q        <@> list sKRM*/128 ->r
  # g           <0> pushmark vRM* ->h
  # o           <1> entersub[t4] vKS*/DREFSV ->p
  # h              <0> pushmark s ->i
  # i              <$> const(PV "attributes") sM ->j
  # j              <$> const(PV "FooBar") sM ->k
  # l              <1> srefgen sKM/1 ->m
  # -                 <1> ex-list lKRM ->l
  # k                    <0> padsv[$bar:493,494] sRM ->l
  # m              <$> const(PV "typed") sM ->n
  # n              <$> method_named(PVIV 1878035063) ->o
  # p           <0> padsv[$bar:493,494] sRM*/LVINTRO ->q

  # z  <;> nextstate(main 530 test.7.pl:34) v
  # 10 <$> const(IV 1) s
  # 11 <0> pushmark vRM*
  # 12 <0> pushmark s
  # 13 <$> const(PV "attributes") sM
  # 14 <$> const(PV "FooBar") sM
  # 15 <0> padsv[$bar:530,532] sRM
  # 16 <1> srefgen sKM/1
  # 17 <$> const(PV "typed") sM
  # 18 <$> method_named(PVIV 1878035063) 
  # 19 <1> entersub[t7] vKS*/DREFSV
  # 1a <0> padsv[$bar:530,532] sRM*/LVINTRO
  # 1b <@> list sKRM*/128
  # 1c <2> sassign vKS/2
  # 1d <;> nextstate(main 531 test.7.pl:36) v

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
    return get_arg_ob($scalars->{$targ}, $op, 'okey') if exists $scalars->{$targ};
    print "debug: list/padsv: undef - targ: $targ name: ", lexicalname($targ), "\n" if $debug;
    get_arg_ob(undef, $self, "non-type-checked scalar: '" . lexicalname($targ) . '"');
  }

  return get_arg_ob(undef, $self, 'unrecognized construct');

}

sub arg_types {

  # method call arguments get checked for types too! woot!
  # given a list of parameter types and a pointer to an op in a bytecode stream, return undef
  # for success or an error message if there is a type mismatch between the two.

  my $prot = shift;
  my $op = shift;

  if(!$op and scalar(@$prot)) {
    return "arguments were expected, but none were provided. ";
  }

  # sub { return unless $op->name() eq 'const'; $type = $op->sv()->sv(); return 1; },

  my $index = 0;
  my $left;
  my $rightob; my $right;

  while($op and $op->name() ne 'method_named') {

    return "more parameters passed than expected in prototype. "  if ! exists $prot->[$i];
    # print "debug: considering: ", $op->name(), "\n";

    $left = $prot->[$index];
    goto OKEY unless $left;

    $right = undef;

    $rightob = solve_type($op); $right = $rightob->typeob();
    if($left and ! $right) {
      return "argument number " . ($index + 1) . " must be type '$left' according to prototype. " . $rightob->diagnostics();
    }

    # right->isa(left)
    goto OKEY if $right->type() eq $left;
    goto OKEY if $right->type()->isa($left);
    return "argument number " . ($index + 1) . " type mismatch: must be type '$left'. "; 

    OKEY:
    $op = $op->sibling() or last;
    $index++;

  }

  return "insufficient number of paramenters. " if $index < @$prot;

  return 0; # success

}

sub check_args {

  # someone somewhere found something that looks like a method call.
  # we check the arguments to that method call against the methods prototype.
  # we also make sure that that method has a prototype, is a constructor, or else the
  # method appears in the package via can(), since we don't want to compute inheritance manually.

  my $op = shift;
  my $type = shift;
  my $method = shift;

  # no $op means no arguments were found. this might be what the prototype is looking for! is this safe? XXX

  my $argob;
  $argob = get_arg_ob($methods->{$type}->{$method}, $op, 'okey') if exists $methods->{$type}->{$method}; 
  # if method is 'new' and no type exists, default to the type of the reference
  $argob = get_arg_ob(get_type_ob($type, $type, 'unknown', 0, undef, 'new', 'constructor method'), $op, 'okey') if $method eq 'new';
  # kludge, but inheritance doesn't work otherwise!
  $argob = get_arg_ob(get_type_ob($type, $type, 'unknown', 0, undef, $method, 'inherited/unprototyped method'), $op, 'okey') 
    if $type->can($method); 
  $argob or die "unknown method. methods called on type safe objects " .
                 "must be prototyped with proto(). package: " . $type . ' method: ' . $method . ' ' . nastily;

  # at this point, we know the return type of the method call. now, we check the argument signiture, if there is one.
  # if we cooked up our own because new() wasn't prototyped, then there won't be one. thats okey.

  my $takes = $argob->typeob()->takes();
  if($takes) {
    my $err = arg_types($takes, $argop);
    die $err . " calling $method in $type, " . nastily if $err;
  }

  # success, so far. this is this being assigned to something else, that might conflict.
  return $argob; 

}

sub lexicalname {
  # given a pad number (stored in all perl operators as $op->targ()), return its name.
  # works well - we get "$foo" etc back
  # PVX() returns the string stored in a scalar as null terminated, ignoring the length info, 
  # which is the correct thing to do with pad entries (length info is barrowed for something else).
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

1;

=pod

=head1 NAME

typesafety.pm - compile-time type usage static analysis 

=head1 SYNOPSIS

  package main;
  use typesafety;

  # use typesafety 'summary';

  my FooBar $foo :typed; # alternate syntax:    declare FooBar => my $a;
  my FooBar $bar :typed; # establish type-checked variables
  my BazQux $baz :typed; # my <type/package> <variable> :typed;

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

L<http://www.c2.com/cgi/wiki?NoseJobRefactoring>

L<Class::Contract>, by Damian Conway

L<Object::PerlDesignPatterns>, by myself. 

The test.pl file that comes with this distribution demonstrates exhaustively
everything that is allowed and everything that is not. 

=head1 AUTHOR

Scott Walters - scott@slowass.net

=head1 COPYRIGHT

Distribute under the same terms as Perl itself.

=cut

__END__

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

okey, the old remember-the-reference-passed-through-attributes-and-look-for-it-in-the-symbol-table
trick isn't going to work. perl creates scalars on the fly and populates them with information
from different places. too many temproraries. would have to use globals - yuck. 

the reference we get is essentially useless to us. at check time, all scalars 
point to undef, which they share an instance of, so we can't compare what value
they initially point at. we can't match actual variables as those are created on the
fly when padsv runs. 

have to do pure static analysis and forget or downplay attributes.

one working idea: use file/line number information. dangerous, kludgey. record file/line from
caller() when attributes are registered, along with the required type. at check time,
we just have to check what is being assigned based on line/file from nextstate.


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

I think the problem we're having with matching pads up to scalars is that we're
getting the scratch pad entry itself, not the value to which it points. This
is pretty clear since the variables name is stored in there.

Okey, past that. Still trying to replicate \$foo.

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

----------

# $baz = $foo->new(); 

2n <;> nextstate(main 556 test.pl:58) v
2o <0> pushmark s
2p <0> padsv[$foo:552,558] sM
2q <$> method_named(PVIV "new") s
2r <1> entersub[t15] sKS/TARG
2s <0> padsv[$baz:554,558] sRM*
2t <2> sassign vKS/2

------------

# $bar = $foo->foo($foo, 1, $bar, $baz, 2, 3, lala());

23 <;> nextstate(main 547 test.8.pl:39) v
24 <0> pushmark s
25 <0> padsv[$foo:544,548] sM                # $foo->
26 <0> padsv[$foo:544,548] lM                # ($foo,
27 <$> const(IV 1) sM                        # 1
28 <0> padsv[$bar:545,548] lM                # $bar
29 <0> padsv[$baz:546,548] lM                # $baz
2a <$> const(IV 2) sM                        # 2
2b <$> const(IV 3) sM                        # 3
2c <0> pushmark s                            # lala()
2d <$> gv(*lala) s/EARLYCV                   #  "
2e <1> entersub[t12] lKMS/NO(),TARG,INARGS,1 # "
2f <$> method_named(PVIV "foo") s            # foo(
2g <1> entersub[t13] sKS/TARG                # "
2h <0> padsv[$bar:545,548] sRM*              # $bar =
2i <2> sassign vKS/2                         # "
2j <;> nextstate(main 548 test.8.pl:43) v

# from arg_types():
# use solve_type() recursively instead...

    if($op->name() eq 'padsv') {
      $right = $scalars->{$op->targ()} if $op->name() eq 'padsv' and exists $scalars->{$op->targ()};
      $left and ! $right and return "argument number " . ($index + 1) . " must be type $left according to prototype. ";
    } elsif($op->name() eq 'const') {
      return sprintf "argument number %d, constant '%s' found where type '%s' expected. ", $index+1, $op->sv()->sv(), $left;
    } # elsif($op->name() eq 

  # c           <0> pushmark s ->d
  # d           <0> padsv[$a:3,5] sM ->e
  # e           <$> const(IV 5) sM ->f
  # f           <$> const(IV 4) sM ->g
  # g           <$> const(IV 3) sM ->h
  # h           <$> const(IV 2) sM ->i
  # i           <$> const(IV 1) sM ->j
  # j           <$> method_named(PVIV "bar") s ->k


--------
Perl stores an amazing amount of data in the bytecode tree. This makes
static analysis both a joy and a fertile field of study. 

A few this are missing. C<my FooBar $c> doesn't record "FooBar" unless an
attribute is included: C<my FooBar $c :typed>.

Source filters can do some things that the B modules can't. L<Acme::Bleach>
operates on something radically different than Perl. L<Sub::Lexical>
extends the syntax beyond what Perl is capable of.
See L<Filter::Simple> for information on source filters.

See perldoc B and L<B::Generate> for more information on Perl's bytecode
interpreter, B.


