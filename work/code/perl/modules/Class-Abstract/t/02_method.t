use Test::More tests => 21;

use_ok('Class::Abstract');

ok(my $A = Class::Abstract::Tag->new('A'), 'new tag');
ok(my $B = Class::Abstract::Tag->new('B', 'A'), 'new tag');
ok(my $C = Class::Abstract::Tag->new('C', 'A'), 'new tag');
ok(my $D = Class::Abstract::Tag->new('D', 'B', 'C'), 'new tag');
ok(my $E = Class::Abstract::Tag->new('E', 'C'), 'new tag');

ok(my $meth = Class::Abstract::Method->new('foo', 2), 'new method');
$meth->add_variant('A', 'A', sub { 'AA' });
$meth->add_variant('B', 'C', sub { 'BC' });
$meth->add_variant('C', 'B', sub { 'CB' });

ok(my $oA = Class::Abstract::Object::Meta->new('A'), 'new object');
ok(my $oB = Class::Abstract::Object::Meta->new('B'), 'new object');
ok(my $oC = Class::Abstract::Object::Meta->new('C'), 'new object');
ok(my $oD = Class::Abstract::Object::Meta->new('D'), 'new object');
ok(my $oE = Class::Abstract::Object::Meta->new('E'), 'new object');

is($oA->foo($oA), 'AA', 'base variant');
is($oA->foo($oB), 'AA', 'base variant');
is($oB->foo($oA), 'AA', 'base variant');
is($oB->foo($oC), 'BC', 'direct');
is($oC->foo($oB), 'CB', 'direct');
is($oB->foo($oE), 'BC', 'derived');
is($oE->foo($oB), 'CB', 'derived');
ok(! eval { $oD->foo($oD); 1 }, 'ambiguous');

$meth->add_variant('D', 'D', sub { 'DD' });
is($oD->foo($oD), 'DD', 'post-compile add');

# vim: ft=perl :
