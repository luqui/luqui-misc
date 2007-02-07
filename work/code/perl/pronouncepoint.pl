#!/usr/bin/perl

use strict;

sub pronounce {
	my ($n) = @_;
	if ($n < 0) {
		return "negative " . pronounce(-$n);
	}
	elsif ($n >= 1000) {
		my @logs = qw{XXX thousand million billion trillion quadrillion quintillion};
		my $log = log($n) / log(1000);
		my $base = 1000**int($log);
		return pronounce(int($n / $base)) . " $logs[$log]" .
		       ($n % $base == 0 ? "" : " " . pronounce($n % $base));
	}
	elsif ($n >= 100) {
		return pronounce(int($n / 100)) . " hundred" . 
			   ($n % 100 == 0 ? "" : " " . pronounce($n % 100));
	}
	elsif ($n >= 20) {
		my @tens = qw{XXX XXX twenty thirty forty fifty sixty seventy eighty ninety};
		return $tens[int($n/10)] . ($n % 10 == 0 ? "" : " " . pronounce($n % 10));
	}
	elsif ($n >= 10) {
		my @teens = qw{ten eleven twelve thirteen fourteen fifteen sixteen
					   seventeen eighteen nineteen};
		return $teens[$n-10];
	}
	else {
		my @ones = qw{zero one two three four five six seven eight nine};
		return $ones[$n];
	}
}

sub fixpoint {
	my ($cur) = @_;
	my %seen;
	while (1) {
		my $say = pronounce($cur);
        print "  $say\n";
		return $say if $seen{$say}++;
		$cur = length $say;
	}
}

for (0..5000) {
	print length(fixpoint($_)), "\n";
}
