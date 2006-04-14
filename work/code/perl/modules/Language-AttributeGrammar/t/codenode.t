use Test::More tests => 2;
use List::Util ();

BEGIN { use_ok('Language::AttributeGrammar') }

sub mko { my $c = shift; bless { @_ } => $c }

my $grammar = <<'EOG';

Leaf:   $/.min = { $<value> }
Branch: $/.min = { List::Util::min(`@{$<children>}`.min) }

Branch: `@{$<children>}`.gmin = { ($/.gmin) x @{$<children>} }
ROOT: $/.gmin = { $/.min }

Leaf:   $/.sum = { $/.gmin }
Branch: $/.sum = { List::Util::sum(`@{$<children>}`.sum) }

EOG

my $ag = Language::AttributeGrammar->new($grammar);
my $sum = $ag->apply(
	mko(Branch => 
		children => [ mko(Branch =>
					      children => [ mko(Leaf => value => 4),
						                mko(Leaf => value => 3) ]),
					  mko(Leaf => value => 7) ],
		), 'sum');
is($sum, 12, "correct result");

# vim: ft=perl :
