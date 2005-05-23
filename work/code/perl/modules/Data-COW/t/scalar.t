use Test::More tests => 6;
BEGIN { use_ok('Data::COW'); }

my $base = 42;
my $scalar = \$base;

my $new = make_cow_ref $scalar;

ok(tied $$new, "tie worked");

is($$new, 42, "new array reflects old one");
is($$scalar, 42, "original is untouched");

$$new = 43;
is($$new, 43, "successfully changed");
is($$scalar, 42, "original is untouched");

# vim: ft=perl :
