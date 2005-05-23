#! /usr/bin/perl -w

N: for (1..500) {
	for my $div (2..$_-1) {
		next N if $_ % $div == 0;
	}
	print "$_ is prime\n";
}
