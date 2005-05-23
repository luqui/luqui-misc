#!/usr/bin/perl

package Tier;

sub TIESCALAR {
    bless { } => 'Tier';
}

sub FETCH {
    print "FETCH\n";
}

sub STORE {
    print "STORE\n";
}

sub make {
    tie $_[1] => 'Tier';
}

package main;

my $foo;
print "$foo\n";
print "Make\n";
Tier->make($foo);
print "Done\n";
print "$foo\n";
