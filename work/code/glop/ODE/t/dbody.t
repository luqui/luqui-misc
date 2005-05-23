use Test::More tests => 8;

BEGIN { use_ok('ODE') };

ok(my $world = ODE::World->new, "dWorldCreate");

ok(my $body = $world->new_body, "dBodyCreate");
$body->position(ODE::Vector->new(4, -5.5, 6.66));
my $vec = $body->position;
cmp_ok($vec, '==', ODE::Vector->new(4, -5.5, 6.66), "dBody*Position");

$body->velocity(ODE::Vector->new(-2, 3.4, -6e7));
$vec = $body->velocity;
cmp_ok($vec, '==', ODE::Vector->new(-2, 3.4, -6e7), "dBody*LinearVel");

$body->angular_velocity(ODE::Vector->new(9, 8, 7));
$vec = $body->angular_velocity;
cmp_ok($vec, '==', ODE::Vector->new(9, 8, 7), "dBody*AngularVel");

{
    my $ref1 = $world->new_body;
    my $ref2 = $ref1;
    $ref1->destroy;
    is(ref($ref1), "ODE::Null", "Null");
    is(ref($ref2), "ODE::Null", "Nonlocal Null");
}

# vim: ft=perl :
