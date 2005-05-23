use Test::More tests => 9;

BEGIN { use_ok('Data::COW') }

my $base = {
    two     => [ 2, 4, 6, 8, 10, 12, 14 ],
    three   => [ 3, 6, 9, 12, 15 ],
    five    => [ 5, 10, 15 ],
    seven   => [ 7, 14 ],
    eleven  => [ 11 ],
    thirten => [ 13 ],
};

my $first  = make_cow_ref $base;
my $second = make_cow_ref $first;

ok(tied %$first, "tied okay");
ok(tied %$second, "tied okay");

push @{$first->{two}}, 16, 18, 20;
is($first->{two}[9], 20, "pushed");
is($second->{two}[9], 20, "change reflected");

push @{$second->{three}}, 18;
is($second->{three}[5], 18, "pushed");
is($first->{three}[5], undef, "change not reflected");

push @{$first->{three}}, 19;
is($first->{three}[5], 19, "pushed");
is($second->{three}[5], 18, "change not reflected");


# vim: ft=perl :
