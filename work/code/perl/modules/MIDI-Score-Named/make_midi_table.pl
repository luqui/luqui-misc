#!/usr/bin/perl

open my $pd, '-|', 'perldoc', '-u', 'MIDI::Score' 
    or die "Couldn't fork perldoc: $!";

print <<'EOM';
package MIDI::Score::Named;
use 5.6.1;

use strict;
use warnings;

our %NAME_TO_INDEX = (
EOM
    
while (<$pd>) {
    if (s/^=item \s+ \('(\w+)', \s* I<(starttime)>//x) {
        my $name = $1;
        my @ind = ('type', 'starttime');
        my $count = 2;
        while (s/^, \s* I<(\w+)>//x) {
            $ind[$count++] = $1;
        }
        print "    $name => {\n";
        print "        $ind[$_] => $_,\n" for 0..$#ind;
        print "    },\n";
    }
}

print <<'EOM';
);

1;
EOM
