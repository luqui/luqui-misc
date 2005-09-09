use Test::More tests => 6;

BEGIN { use_ok('Data::Histogram') }

my $hist = histogram 1, 3, 1, 'hi', 4, 3, 'hi';
is($hist->lookup(1),     2, "lookup");
is($hist->lookup(3),     2, "lookup");
is($hist->lookup('hi'),  2, "lookup");
is($hist->lookup(4),     1, "lookup");
is($hist->lookup('foo'), 0, "lookup");

# vim: ft=perl :
