use Test::More tests => 3;

BEGIN { use_ok('ODE') }

ok(my $world = ODE::World->new, "dWorldCreate");

{
    $world->gravity(ODE::Vector->new(0, -9.8, 0));
    my @vec = $world->gravity->list;
    ok(    $vec[0] == 0
        && $vec[1] == -9.8
        && $vec[2] == 0,      "dWorld*Gravity");
}

# vim: ft=perl :
