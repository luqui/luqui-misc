use strict;
use warnings;

use Test::More tests => 3;

BEGIN { use_ok('Language::AttributeGrammar') }

package Destroyer;

sub new {
	my ($class, $value, $destroy) = @_;
	bless { value => $value, destroy => $destroy } => ref $class || $class;
}

sub value {
	my ($self) = @_;
	$self->{value};
}

sub DESTROY {
	my ($self) = @_;
	$self->{destroy}->();
}

package main;

use List::Util ();

sub mko { my $c = shift; bless { @_ } => $c }
our $destroyed = 0;

my $findmin = <<'EOG';
Leaf:   $/.min = { Destroyer->new($<value>, sub { $::destroyed++ }) }
Branch: $/.min = { Destroyer->new(List::Util::min($<left>.min->value, $<right>.min->value), sub { $::destroyed++ }) }
ROOT:   $/.result = { my $min = $/.min;
                      Test::More::is($::destroyed, 6, "correct number of destructions so far"); 
					  $min->value }
EOG

my $ag = Language::AttributeGrammar->new($findmin);
is($ag->apply(mko(Branch => 
			        left => mko(Branch => 
								  left => mko(Leaf => value => 1),
								  right => mko(Leaf => value => 2),
								),
					right => mko(Branch =>
								  left => mko(Leaf => value => 3),
								  right => mko(Leaf => value => 4),
								)),
			  'result'),
		  1, "correct result");

# vim: ft=perl :
