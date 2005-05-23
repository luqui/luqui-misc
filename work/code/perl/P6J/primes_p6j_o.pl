#! /usr/bin/perl -w

use Perl6::Junctions;

$allprimes = 2;

for (3..500) {
	if ($_ % $allprimes) {
		print "$_ is prime\n" ;
		$allprimes &= $_;
	}
}

