use Test::More tests => 10;
use Data::Dumper;

BEGIN { use_ok('Class::Multimethods::Pure') }

ok(my $method = Class::Multimethods::Pure::Method->new(name => 'foo'), 'New method');

my $sref = \my $sderef;
my @vars = (
    [ 'A', '$', "Hello" ],
    [ 'B', '#', "345" ],
    [ 'C', 'ARRAY', [1,2,3] ],
    [ 'D', 'HASH', { a => 'b' } ],
    [ 'E', 'SCALAR', $sref ],
    [ 'F', 'GLOB', \*STDOUT ],
    [ 'G', 'REF', \$sref ],
    [ 'H', 'CODE', sub { 42 } ],
);

for (@vars) {
    my $cur = $_;
    $method->add_variant(sub { $cur->[0] }, [ $cur->[1] ]);
}

for (@vars) {
    is($method->find_variant([$_->[2]])->code->($_->[2]), $_->[0], 'Matches');
}

# vim: ft=perl :
