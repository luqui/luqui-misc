#!/usr/bin/perl

package GVT;

sub DESTROY {
    print "GVT::DESTROY\n";
}

sub make {
    # We have determined that this is _not_ the same as tying
    bless \$_[1] => 'GVT';
}

package A;

sub DESTROY {
    print "A::DESTROY\n";
}

sub new {
    bless { } => ref $_[0] || $_[0];
}

sub from {
    print "Farg = " . \$_[0] . "; $_[0]\n";
}

package main;

my A $foo = A->new;

my $bar = $foo;

GVT->make($foo);
GVT->make($bar);

$foo->from;
$bar->from;
$foo->from;
