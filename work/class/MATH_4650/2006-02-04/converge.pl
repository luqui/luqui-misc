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
    return abs(($a-$b)/$a) < 1e-12;
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

my $pi = 4*atan2(1,1);

my $term = Term::ReadLine::Gnu->new;

my $fntxt = $term->readline('f($x) = ');
my $fn = eval "sub { my \$x = shift; $fntxt }" 
            or die "Failed parse: $@";
my $fptxt = $term->readline('f\'($x) = ');
my $fp = eval "sub { my \$x = shift; $fptxt }" 
            or die "Failed parse: $@";

while (my $intxt = $term->readline('Initial guess = ')) {
    print newton($fn, $fp, $intxt), "\n";
}
