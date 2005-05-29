use Test::More tests => 20;

BEGIN { use_ok('ODE') }

ok(defined(my $z = ODE::Vector->new), "new");
ok(defined(my $v = ODE::Vector->new(2,3,6)), "new");

is("$z", "<0,0,0>", "str");
is("$v", "<2,3,6>", "str");

is([ $v->list ]->[0], $v->[0], "list/deref");

cmp_ok($z->norm, '==', 0, "norm");
cmp_ok($v->norm, '==', 7, "norm");

cmp_ok($v, '==', ODE::Vector->new(2,3,6), "==");
cmp_ok($v, '!=', ODE::Vector->new(3,4,5), "!=");

cmp_ok($z + $v, '==', $v, "+");
cmp_ok($v + ODE::Vector->new(1,2,3), '==', ODE::Vector->new(3,5,9));

cmp_ok($v * 2, '==', ODE::Vector->new(4, 6, 12), "scale");
cmp_ok(2 * $v, '==', ODE::Vector->new(4, 6, 12), "scale");
cmp_ok($v / 2, '==', ODE::Vector->new(1, 1.5, 3), "scale(div)");

cmp_ok($z * $v, '==', 0, "dot");
cmp_ok($v * ODE::Vector->new(1/2, 1/3, 1/6), '==', 3, "dot");

eval {
    if ($v == 0) { print "Oh no!\n" }
};
ok($@, "compare vector and scalar");

my $vc = $v;
$v += ODE::Vector->new(1,0,0);
cmp_ok($v, '==', ODE::Vector->new(3,3,6), "+=");
cmp_ok($vc, '==', ODE::Vector->new(2,3,6), "value");

# vim: ft=perl :
