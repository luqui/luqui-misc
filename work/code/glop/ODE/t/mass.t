use Test::More tests => 5;

use_ok('ODE');

ok(my $mass = ODE::Mass->new(4), "new");

cmp_ok($mass->mass, '==', 4, "mass");
$mass->mass(6);
cmp_ok($mass->mass, '==', 6, "set_mass");

$mass->center_of_gravity(ODE::Vector->new(3,4,5));
cmp_ok($mass->center_of_gravity(), '==', ODE::Vector->new(3,4,5), "center_of_gravity");

# vim: ft=perl :
