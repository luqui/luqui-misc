#!/usr/bin/perl

use strict;
use Term::ReadLine;

sub bisect {
    my ($func, $lo, $hi, $accuracy) = @_;
    die "Bounds do not satisfy constrants" 
        unless $func->($lo) * $func->($hi) < 0;
        
    if ($func->($lo) > 0) { 
        ($lo, $hi) = ($hi, $lo);   # make sure $func->($lo) < 0
    }

    while (abs($hi - $lo) > $accuracy) {
        print "  [$lo, $hi]\n";
        my $mid = ($hi + $lo) / 2;
        if ($func->($mid) < 0) {
            $lo = $mid;
        }
        elsif ($func->($mid) > 0) {
            $hi = $mid;
        }
        else {   # $func->($mid) == 0
            return $mid;
        }
    }
    return(($hi + $lo) / 2);
}

my $term = Term::ReadLine::Gnu->new;

my $fntxt = $term->readline('f($x) = ');
my $fn = eval "sub { my \$x = shift; $fntxt }" 
            or die "Failed parse: $@";

while (my $intxt = $term->readline('Interval = ')) {
    unless ($intxt =~ /^ \s* \[ 
                        \s* (-?\d+\.\d+) \s* , 
                        \s* (-?\d+\.\d+) \s* 
                      \] \s* $/x) {
        print "Bad interval\n";  next;
    }
    print bisect($fn, $1, $2, 1e-2), "\n";
}
