use Test::More tests => 8;

BEGIN { use_ok('ODE') }

my $EPSILON = 0.0005;
sub numeq {
    my ($a, $b) = @_;
    abs($a - $b) < $EPSILON;
}

ok(my $I = ODE::Quaternion->new, "new");
ok(my $q = ODE::Quaternion->new(1, [0, 0, 1]), "new");

ok(numeq($I->angle, 0), "angle");
ok(numeq($q->angle, 1), "angle");
cmp_ok($q->axis, '==', ODE::Vector->new(0, 0, 1), "axis");

ok(numeq(($q * $q)->angle, 2), "*");
cmp_ok(($q * $q)->axis, '==', ODE::Vector->new(0, 0, 1), "*");

# vim: ft=perl :
