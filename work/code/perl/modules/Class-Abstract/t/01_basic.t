use Test::More tests => 43;

use_ok('Class::Abstract');

ok(my $A = Class::Abstract::Tag->new('A'), 'new Tag');
ok(my $B = Class::Abstract::Tag->new('B', 'A'), 'new Tag with parent');
ok(my $C = Class::Abstract::Tag->new('C', 'A'), 'more Tags');
ok(my $D = Class::Abstract::Tag->new('D', 'B'), 'more Tags');

ok($B->is_ancestor('A'), 'ancestor');
ok($B->is_ancestor($A), 'ancestor, ref variant');
ok(!$A->is_ancestor('B'), 'reverse ancestor');
ok($A->is_ancestor('A'), 'self ancestor');
ok($B->is_ancestor('B'), 'self ancestor');
ok($D->is_ancestor('B'), 'ancestor');
ok($D->is_ancestor('A'), 'deep ancestor');

ok(my $meth = Class::Abstract::Method->new('foo', 2), 'new Method');
$meth->add_variant('A', 'A', sub { });  # 0
$meth->add_variant('B', 'C', sub { });  # 1
$meth->add_variant('C', 'B', sub { });  # 2
$meth->add_variant('D', 'C', sub { });  # 3

# add_variant topologically sorts them, and this is what they should
# come out to be
is($meth->variant_sig(0), 'foo(D, C)', 'sig & ordering');  # variant 0
is($meth->variant_sig(1), 'foo(B, C)', 'sig & ordering');  # variant 1
is($meth->variant_sig(2), 'foo(C, B)', 'sig & ordering');  # variant 2
is($meth->variant_sig(3), 'foo(A, A)', 'sig & ordering');  # variant 3

is_deeply([ map { $_->to_Hex } @{$meth->make_bits('A')} ], [ '8', '8' ], 'make_bits');
is_deeply([ map { $_->to_Hex } @{$meth->make_bits('B')} ], [ 'A', 'C' ], 'make_bits');
is_deeply([ map { $_->to_Hex } @{$meth->make_bits('C')} ], [ 'C', 'B' ], 'make_bits');
is_deeply([ map { $_->to_Hex } @{$meth->make_bits('D')} ], [ 'B', 'C' ], 'make_bits');

##### 21 tests so far #####

# 16 automatic tests follow
my %includes = map { $_ => 1 } 
               qw{ 3;0 3;1 3;2 1;0 };
for my $a (0..3) {
    for my $b (0..3) {
        ok(! ! $includes{"$a;$b"} == ! ! $meth->variant_includes($a, $b), 
            "autotest includes $a;$b");
    }
}

##### 37 tests so far #####

is_deeply([ sort $meth->find_variants(1, [ 'A' ], [ 'A' ]) ], [ 3 ], "direct lookup");
is_deeply([ sort $meth->find_variants(1, [ 'B' ], [ 'C' ]) ], [ 1 ], "direct lookup");
is_deeply([ sort $meth->find_variants(1, [ 'C' ], [ 'B' ]) ], [ 2 ], "direct lookup");
is_deeply([ sort $meth->find_variants(1, [ 'D' ], [ 'C' ]) ], [ 0 ], "direct lookup");

is_deeply([ sort $meth->find_variants(1, [ 'D' ], [ 'D' ]) ], [ 3 ], "lookup");
is_deeply([ sort $meth->find_variants(1, [ 'C', 'D' ], [ 'C', 'D' ]) ], [ 0, 2 ], "lookup");

# vim: ft=perl :
