#! /usr/bin/perl -w

use Perl6::Junctions -operators;

for (1..500) {
	print "$_ is prime\n" 
		if $_ % all(2..$_-1) != 0;
}
