#!/usr/bin/perl

sub onetwo {
    for (1..2) {
        $_[0]->($_);
    }
}

for (3..4) {
    onetwo(sub { next; print " $_[0]\n" });
    print "$_\n";
}
