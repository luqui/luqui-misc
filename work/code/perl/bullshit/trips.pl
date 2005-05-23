#!/usr/bin/perl

my $tot;
my $trips;
while (<>) {
    $tot++;
    my @c = map { (/(.)/)[0] } split;
    if (@c == 5) {
        if (
            $c[0] eq $c[1] && $c[1] eq $c[2] ||
            $c[0] eq $c[1] && $c[1] eq $c[3] ||
            $c[0] eq $c[1] && $c[1] eq $c[4] ||
            $c[0] eq $c[2] && $c[2] eq $c[3] ||
            $c[0] eq $c[2] && $c[2] eq $c[4] ||
            $c[0] eq $c[3] && $c[3] eq $c[4] ||
            $c[1] eq $c[2] && $c[2] eq $c[3] ||
            $c[1] eq $c[2] && $c[2] eq $c[4] ||
            $c[1] eq $c[3] && $c[3] eq $c[4] ||
            $c[2] eq $c[3] && $c[3] eq $c[4] ) {
                print "@c\n";
                $trips++;
        }
    }
}

print "$trips/$tot\n";
