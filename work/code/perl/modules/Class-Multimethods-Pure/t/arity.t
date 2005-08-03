use Test::More tests => 7;

BEGIN { use_ok('Class::Multimethods::Pure') }

multi foo => (Any) => sub { "ok @_" };

is(foo(1), "ok 1", "sanity check");
is(foo(1,2), "ok 1 2", "can pass additional arguments");
ok(!eval { foo(); 1 }, "no arguments dies");

package Foo;
sub new { bless {} => shift }
package Bar;
sub new { bless {} => shift }
package main;

multi bar => (Foo) => sub { "one" };
multi bar => (Foo, Foo) => sub { "two" };

is(bar(Foo->new),           "one", "single argument");
is(bar(Foo->new, Foo->new), "two", "double argument");
is(bar(Foo->new, Bar->new), "one", "single argument+extraneous");

# vim: ft=perl :
