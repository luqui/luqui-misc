use Test::More tests => 4;
use Data::Dumper;

BEGIN { use_ok('Class::Multimethods::Pure') }

package Foo;
package Bar;
package main;

ok(my $method = Class::Multimethods::Pure::Method->new(name => 'foo'), 'New method');

$method->add_variant(sub { 'A' }, [ 'Foo' ]);
$method->add_variant(sub { 'B' }, [ 'Bar' ]);

my $foo = bless {} => 'Foo';
my $bar = bless {} => 'Bar';

is($method->find_variant([ $foo ])->code->(), 'A', 'SMD');
is($method->find_variant([ $bar ])->code->(), 'B', 'SMD');

# vim: ft=perl :
