#!/usr/bin/perl

use strict;
use Perl6::Placeholders;

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

sub bisection {
    my ($f, $lo, $hi) = @_;
    die "bisection: Usage: bisection(func, lower bound, upper bound)\n"
        unless $f->($lo) < 0 && $f->($hi) > 0;

    my $mid  = $hi;
    my $prev;
    while (1) {
        $prev = $mid;
        $mid = ($hi+$lo)/2;
        
        if (checkconv($mid, $prev)) { last; }
        elsif ($f->($mid) < 0)      { $lo = $mid; }
        else                        { $hi = $mid; }
    }
    return checkzero($f, $mid);
}

sub newton {
    my ($f, $df, $p0) = @_;
    my $p = $p0;
    my $prev;
    
    while (1) {
        $prev = $p;
        $p -= $f->($p) / $df->($p);
        
        last if checkconv($p, $prev);
    }
    return checkzero($f, $p);
}

my $pi = 4*atan2(1,1);
print bisection({ sin($^x) }, 3*$pi/2, $pi/2), "\n";
print newton({ sin($^x) }, { cos($^x) }, $pi/2+0.5), "\n";
