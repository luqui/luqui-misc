use Test::More tests => 3;
use Data::Dumper;

BEGIN { use_ok('Class::Multimethods::Pure') }

package Foo;
package Bar;
package main;

multi foo => Foo => sub { 'A' };
multi foo => Bar => sub { 'B' };

my $foo = bless {} => 'Foo';
my $bar = bless {} => 'Bar';

is(foo($foo), 'A', 'SMD');
is(foo($bar), 'B', 'SMD');

# vim: ft=perl :
