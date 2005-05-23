#!/usr/bin/perl

use strict;

my $pokenum = '/home/fibonaci/dl/poker-eval-124.0/examples/pokenum';

my @names = qw<2 3 4 5 6 7 8 9 T J Q K A>;

sub runenum {
    my ($handa, $handb) = @_;
    my $ev = qx/$pokenum $handa - $handb/;
    if ($ev =~ /^Holdem Hi: (\d+) enumerated boards\n.*?\n\S\S \S\S\s+(\d+).*?\n\S\S \S\S\s+(\d+)/) {
        print "  $handb $2 $3 / $1\n";
    }
}

sub enum {
    my ($handa) = @_;
    print "$handa\n";
    
    my @suitperms;
    if ($handa =~ /.c .c/)  { # suited
        @suitperms = (
            [ 'c', 'c' ],
            [ 'h', 'h' ],
            [ 'c', 'h' ],
            [ 'h', 'c' ],
            [ 'h', 's' ],
        );
    }
    else {
        @suitperms = (
            [ 'c', 'c' ],
            [ 'd', 'd' ],
            [ 'c', 'd' ],
            [ 'd', 'c' ],
            [ 'h', 'h' ],
            [ 'c', 'h' ],
            [ 'h', 'c' ],
            [ 'd', 'h' ],
            [ 'h', 'd' ],
            [ 'h', 's' ],
        );
    }

    for my $b1 (0..$#names) {
        for my $b2 ($b1..$#names) {
            for my $perm (@suitperms) {
                next if $b1 == $b2 && $perm->[0] eq $perm->[1];
                my $handb = "$names[$b1]$perm->[0] $names[$b2]$perm->[1]";
                runenum($handa, $handb);
            }
        }
    }
}

my $ptime = time;

for my $a1 (0..$#names) {
    for my $a2 ($a1..$#names) {
        if ($a1 != $a2) {
            my $handa = "$names[$a1]c $names[$a2]c";
            print STDERR "$handa (" . (time - $ptime) . "s)\n";
            $ptime = time;
            enum $handa;
        }
        my $handa = "$names[$a1]c $names[$a2]d";
        print STDERR "$handa (" . (time - $ptime) . "s)\n";
        $ptime = time;
        enum $handa;
    }
}
