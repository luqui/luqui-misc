#!/usr/bin/perl

for my $lockers (1..1024) {
    my @l;
    for $i (1..$lockers) {
        for (my $j = 0; $j < $lockers; $j += $i) {
            $l[$j] ^= 1;
        }
    }

    print join(' ', map { $l[$_] ? $_ : () } 1..$#l), "\n";
}
