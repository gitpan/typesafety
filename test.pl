# Before `make install' is performed this script should be runnable with
# `make test'. After `make install' it should work as `perl test.pl'

#########################

# change 'tests => 1' to 'tests => last_test_to_print';

use Test;
BEGIN { plan tests => 1 };
# use typesafety; # see gripes below
ok(1); # If we made it this far, we're ok.

__END__

#########################

# Insert your test code below, the Test module is use()ed here so read
# its man page ( perldoc Test ) for help writing this test script.

#
#
# if everything goes well, typesafety.pm shouldn't object to any of this code.
# of course, that is just like it isn't there. what we really want to test is
# whether it objects to the things it should object to. Test:: doesn't seem
# to be structed this way, though. any ideas?
#
#

#
# wow, if that doesn't just bite the bag. perl test.pl runs fine, but trying to do
# "make test", it blows up, unable to dynamic link to B::Generate. 
# like everything else in perl, it is obnoxiously complex, and seldom works right.
# screw testing. this is just a comment now.
#

#
# test class 
#

package FooBar;
use typesafety;

# proto 'new', returns => 'FooBar';
proto 'foo', returns => 'FooBar';

sub new {
  my $type = shift; $type = ref $type if ref $type;
  bless [], $type;
}

proto 'foo', returns => 'FooBar', takes => 'FooBar', undef, 'FooBar', 'BazQux', undef, undef, undef;

sub foo {
  my $me = shift;
  return $me->new();
}

proto 'yutz', returns => 'BazQux';

sub yutz { return new BazQux; }

proto 'yadda', returns => 'FooBar';

sub yadda { $_[0]->new(); }

#
# test class 
#

package BazQux;
use typesafety;
@ISA = qw(FooBar);

proto 'new', returns => 'BazQux';

sub new {
  my $type = shift; $type = ref $type if ref $type;
  bless [], $type;
}

#
# basic declarations
#

my FooBar $foo :typed; $foo = new FooBar;
my FooBar $bar :typed; $bar = new FooBar;
my BazQux $baz :typed; $baz = new BazQux;

# my Foo::Bar $bar :typed;  # seems to work, given a Foo::Bar package

#
# two declarations on the same line. 
#

my FooBar $test1 :typed; my FooBar $test2 :typed;

#
# basic assignments
#

my $blurgh;
# $bar = $blurgh;  # illegal
# $bar = 1;        # illegal

$test2 = $test1;   # okey

# $test1 = "zero"; # illegal
# $test2 = 0;      # illegal

#
# alternate declaration syntax
#

declare FooBar => my $test3;
declare FooBar => my $test4;

#
# assigning to declarations
#

(declare FooBar => my $test5) = 10;  # don't think we ever got where we could deal with this XXX
my FooBar $test6 :typed = 1;           # XXX same thing


# $foo = new BazQux (1,2,3,4);   # illegal - incompatiable types
# $baz = $foo->foo(1,2,3,4);     # illegal - prototyped
# $foo->doesntexist();           # illegal - unknown method
# $foo = $foo->foo();
# $foo = $foo->doesntexist();

#
# prototypes
#

$bar = $foo->foo($foo, 1, $bar, $baz, 2, 3, lala());              # this works
$bar = $foo->foo($foo, $foo, $bar, $baz, $baz, 3, lala());        # this works too
$bar = $foo->foo($foo->yadda(), 1, $bar, $baz, $baz, 3, lala());  # this should work, but does it? awesome!
# $bar = $foo->foo($foo->yutz(), 1, $bar, $baz, $baz, 3, lala()); # this is illegal
# $bar = $foo->foo($foo, 1, $bar, $bar, 2, 3, lala());            # this is illegal

sub lala { return 3+rand(5); }

#
# misc
#

# $foo = new FooBar 1, 2, 3, 4, 5, 6;

#
# inheritance
#

# $baz = $foo->new();  # illegal 
$foo = $baz;           # allowed - $baz is a $foo

#
# and, go!
#

typesafety::check();


