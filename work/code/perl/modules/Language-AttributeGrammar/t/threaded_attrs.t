use Test::More tests => 3;

BEGIN { use_ok('Language::AttributeGrammar') }

my $grammar = new Language::AttributeGrammar <<'EOG';
Root: count($.tree) = { 0 }

Leaf: count($$) = { count($$) + 1 }
Branch: count($.left) = { count($$) } 
Branch: count($.right) = { count($.left) }

# reconstruct the minimized result
Root: result($$) = { bless { tree => result($.tree) } => 'Root' }
Leaf: result($$) = { bless { value => count($$) } => 'Leaf' }
Branch: result($$) = { bless { left  => result($.left), 
                               right => result($.right) } => 'Branch' }

EOG

sub Leaf   { bless { value => $_[0] } => 'Leaf' }
sub Branch { bless { left => $_[0], right => $_[1] } => 'Branch' }
sub Root   { bless { tree => $_[0] } => 'Root' }

my $tree = Root(Branch(
            Branch(Leaf(2), Leaf(3)),
            Branch(Leaf(1), Branch(Leaf(5), Leaf(9)))));
my $result = Root(Branch(
            Branch(Leaf(1), Leaf(2)),
            Branch(Leaf(3), Branch(Leaf(4), Leaf(5)))));

my $atree = $grammar->apply($tree);

is_deeply($atree->result, $result);
is($atree->count, 5);

# vim: ft=perl :

