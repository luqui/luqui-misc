use Test::More tests => 11;
BEGIN { use_ok('Data::COW'); }

my $hash =  { a => { foo => 1, bar => 2 }, b => { baz => 3, quux => 4, frix => 5 } };
my $base =  { a => { foo => 1, bar => 2 }, b => { baz => 3, quux => 4, frix => 5 } };

my $new = make_cow_ref $hash;

ok(tied %$new, "tie worked");

is($new->{a}{bar}, 2, "new hash reflects old one");
is_deeply($hash, $base, "original is untouched");

$new->{a}{foo} = 2;
is($new->{a}{foo}, 2, "successfully changed");
is_deeply($hash, $base, "original is untouched");

$new->{b}{quux} = 6;
is($new->{b}{quux}, 6, "successfully changed");
is($new->{a}{foo}, 2, "the first one is still changed");

$new->{b}{baz} = 9;
is($new->{b}{baz}, 9, "successfully changed");

$new->{c} = 10;
is($new->{c}, 10, "we actually put something there");
is_deeply($hash, $base, "original is untouched");

# vim: ft=perl :
