#! /usr/bin/perl -w

for my $N (1..500) {
	print "$N is prime\n"
		unless grep { $N % $_ == 0 } 2..$N-1;
}
