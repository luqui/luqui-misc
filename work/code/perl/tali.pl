#!/usr/bin/perl

use strict;

sub max_tuplet {
	my (@roll) = @_;
	my %freq;
	for (@roll) {
		$freq{$_}++;
	}
	my $best = (sort { $freq{$b} <=> $freq{$a} } keys %freq)[0];
	return ($best) x $freq{$best};
}

sub play {
	my (@roll, @keep);
	for (1..3) {
		@roll = @keep;
		push @roll, map { 1 + int rand 6 } @keep..4;
		@keep = max_tuplet @roll;
	}
	if (@keep == 5) { return 1 }
	else            { return 0 }
}

my $total = 0;
for (1..1_000_000) {
	$total += play();
	if ($_ % 1_000 == 0) {
		print "$_ : " . $total / $_ . "\n";
	}
}
