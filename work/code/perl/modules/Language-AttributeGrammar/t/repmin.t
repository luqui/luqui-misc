use Test::More tests => 2;

BEGIN { use_ok('Language::AttributeGrammar') }

my $grammar = new Language::AttributeGrammar <<'EOG';

# find the minimum from the leaves up
Leaf: min($$) = { $.value }
Branch: min($$) = { 
    my ($lmin, $rmin) = (min($.left), min($.right));
    $lmin <= $rmin ? $lmin : $rmin }

# propagate the global minimum downward
Root: gmin($.tree) = { min($.tree) }
Branch: gmin($.left)  = { gmin($$) }
      | gmin($.right) = { gmin($$) }

# reconstruct the minimized result
Leaf: result($$) = { bless { value => gmin($$) } => 'Leaf' }
Branch: result($$) = { bless { left  => result($.left), 
                               right => result($.right) } => 'Branch' }
Root: result($$) = { result($.tree) }

EOG

sub Leaf   { bless { value => $_[0] } => 'Leaf' }
sub Branch { bless { left => $_[0], right => $_[1] } => 'Branch' }
sub Root   { bless { tree => $_[0] } => 'Root' }

my $tree = Root(Branch(
            Branch(Leaf(2), Leaf(3)),
            Branch(Leaf(1), Branch(Leaf(5), Leaf(9)))));
my $result = Branch(
            Branch(Leaf(1), Leaf(1)),
            Branch(Leaf(1), Branch(Leaf(1), Leaf(1))));

my $atree = $grammar->apply($tree);

is_deeply($atree->result, $result);

# vim: ft=perl :
