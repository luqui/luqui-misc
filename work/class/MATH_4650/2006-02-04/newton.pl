#!/usr/bin/perl

use strict;
use Term::ReadLine;

sub checkzero {
    my ($f, $p) = @_;
    # doesn't work if df/dx > 100 at p
    warn "Warning: Did not converge to a zero!\n" 
        unless abs($f->($p)) < 1e-10;  
    return $p;
}

sub checkconv {
    my ($a, $b) = @_;
    return abs($a-$b) < 1e-12;
}

sub newton {
    my ($f, $df, $p0) = @_;
    my $p = $p0;
    my $prev;
    
    while (1) {
        print "  $p\n";
        $prev = $p;
        $p -= $f->($p) / $df->($p);
        
        last if checkconv($p, $prev);
    }
    return checkzero($f, $p);
}

sub secant {
    # basically straight from the book
    my ($f, $p0, $p1) = @_;
    my ($q0, $q1) = ($f->($p0), $f->($p1));
    my $p;
    
    while (1) {
        print "  $p0, $p1\n";
        $p = $p1 - $q1 * ($p1 - $p0) / ($q1 - $q0);
        last if checkconv($p, $p1);
        ($p0, $q0, $p1, $q1) = ($p1, $q1, $p, $f->($p));
    }
    return checkzero($f, $p);
}

my $pi = 4*atan2(1,1);

my $term = Term::ReadLine::Gnu->new;

my $fntxt = $term->readline('f($x) = ');
my $fn = eval "sub { my \$x = shift; $fntxt }" 
            or die "Failed parse: $@";
my $fptxt = $term->readline('f\'($x) = ');
my $fp = eval "sub { my \$x = shift; $fptxt }" 
            or die "Failed parse: $@";

while (my $intxt = $term->readline('Initial guess = ')) {
    if ($intxt =~ s/^secant\s*//) {
        my $intxt2 = $term->readline('Initial guess 2 = ');
        print secant($fn, $intxt, $intxt2), "\n";
    }
    else {
        print newton($fn, $fp, $intxt), "\n";
    }
}
