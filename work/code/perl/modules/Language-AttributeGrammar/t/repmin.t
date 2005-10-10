use Test::More tests => 4;

BEGIN { use_ok('Language::AttributeGrammar') }
BEGIN { use_ok('Language::AttributeGrammar::Engine') }

my $grammar = new Language::AttributeGrammar <<'EOG';

# find the minimum from the leaves up
Leaf: min($$) = { $.value }
Branch: min($$) = { 
    my ($lmin, $rmin) = (min($.left), min($.right));
    $lmin <= $rmin ? $lmin : $rmin }

# propagate the global minimum downward
ROOT:   gmin($$)      = { min($$) }
Branch: gmin($.left)  = { gmin($$) }
      | gmin($.right) = { gmin($$) }

# reconstruct the minimized result
Leaf: result($$) = { bless { value => gmin($$) } => 'Leaf' }
Branch: result($$) = { bless { left  => result($.left), 
                               right => result($.right) } => 'Branch' }

EOG

sub Leaf   { bless { value => $_[0] } => 'Leaf' }
sub Branch { bless { left => $_[0], right => $_[1] } => 'Branch' }

my $tree = Branch(
            Branch(Leaf(2), Leaf(3)),
            Branch(Leaf(1), Branch(Leaf(5), Leaf(9))));
my $result = Branch(
            Branch(Leaf(1), Leaf(1)),
            Branch(Leaf(1), Branch(Leaf(1), Leaf(1))));

my $atree = $grammar->apply($tree);

is_deeply($atree->result, $result);


my $engine = Language::AttributeGrammar::Engine->new;

add_visitor $engine Leaf => sub {
    my ($self, $attrs) = @_;
    $attrs->get($self)->get('min')->set(sub { $self->{value} });
};

add_visitor $engine Branch => sub {
    my ($self, $attrs) = @_;
    my $lmin = $attrs->get($self->{left})->get('min');
    my $rmin = $attrs->get($self->{right})->get('min');
    $attrs->get($self)->get('min')->set(sub { $lmin->get <= $rmin->get ? $lmin->get : $rmin->get });
};

add_visitor $engine ROOT => sub {
    my ($self, $attrs) = @_;
    my $min = $attrs->get($self)->get('min');
    $attrs->get($self)->get('gmin')->set(sub { $min->get });
};

add_visitor $engine Branch => sub {
    my ($self, $attrs) = @_;
    my $gmin = $attrs->get($self)->get('min');
    $attrs->get($self->{left})->get('gmin')->set(sub { $gmin->get });
};

add_visitor $engine Leaf => sub {
    my ($self, $attrs) = @_;
    my $min = $attrs->get($self)->get('gmin');
    $attrs->get($self)->get('result')->set(sub { print "Evaluating $min\n"; Leaf($min->get) });
};

add_visitor $engine Branch => sub {
    my ($self, $attrs) = @_;
    my $left = $attrs->get($self->{left})->get('result');
    my $right = $attrs->get($self->{right})->get('result');
    $attrs->get($self)->get('result')->set(sub { Branch($left->get, $right->get) });
};


$engine->make_visitor('ag_visit');
is_deeply($engine->evaluate('ag_visit', $tree, 'result'), $result);

# vim: ft=perl :
