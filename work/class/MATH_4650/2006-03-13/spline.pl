#!/usr/bin/perl

# Luke Palmer
# MATH 4650
# 2006-03-13

use strict;    

use IO::Prompt;

sub create_spline_constants {
    my ($xref, $yref) = @_;
    my @x = @$xref;
    my @a = @$yref;
    my (@b,@c,@d,@h,@alpha,@l,@mu,@z);
    my $n = @x-1;
    
    # Algorithm from the book.
    # Admittedly I do not understand most of it.
    
    for my $i (0..$n-1) { 
        $h[$i] = $x[$i+1] - $x[$i];
    }
    
    for my $i (1..$n-1) {
        $alpha[$i] = 3/$h[$i]   * ($a[$i+1] - $a[$i]) 
                   - 3/$h[$i-1] * ($a[$i] - $a[$i-1]);
    }

    $l[0] = 1;
    $mu[0] = 0;
    $z[0] = 0;

    for my $i (1..$n-1) {
        $l[$i] = 2*($x[$i+1] - $x[$i-1]) - $h[$i-1] * $mu[$i-1];
        $mu[$i] = $h[$i]/$l[$i];
        $z[$i] = ($alpha[$i] - $h[$i-1]*$z[$i-1]) / $l[$i];
    }

    $l[$n] = 1;
    $z[$n] = 0;
    $c[$n] = 0;

    for my $j (reverse 0..$n-1) {
        $c[$j] = $z[$j] - $mu[$j]*$c[$j+1];
        $b[$j] = ($a[$j+1] - $a[$j]) / $h[$j] - $h[$j] * ($c[$j+1] + 2*$c[$j]) / 3;
        $d[$j] = ($c[$j+1] - $c[$j]) / (3*$h[$j]);
    }

    return (\@a,\@b,\@c,\@d);
}

sub spline_from_constants { 
    my ($xs, $a,$b,$c,$d) = @_;
    sub {
        my ($x) = @_;
        # Locate the index of the piece (making far too many assumptions)
        my $idx = 0;
        for my $i (reverse 1..$#$xs) {
            if ($x >= $xs->[$i]) { $idx = $i; last; }
        }
        
        my $xi = $x - $xs->[$idx];
        return $a->[$idx] + $b->[$idx] * $xi + $c->[$idx] * $xi*$xi + $d->[$idx] * $xi*$xi*$xi;
    };
}

sub spline {
    my ($xs, $ys) = @_;
    my ($a,$b,$c,$d) = create_spline_constants($xs,$ys);
    return spline_from_constants($xs, $a,$b,$c,$d);
}

sub spline_from_function {
    my ($lo, $hi, $n, $f) = @_;
    my @xs = map { ($hi - $lo) * $_ / $n + $lo } 0..$n;
    my @ys = map { $f->($_) } @xs;
    spline(\@xs, \@ys);
}

sub spline_table {
    my ($lo, $hi, $n, $f) = @_;
    printf "%16s | %16s\n", 'x', 'y';
    print "-"x16 . "-+-" . "-"x16 . "\n";
    
    for my $i (0..$n) {
        my $x = ($hi - $lo) * $i / $n + $lo;
        printf "%16f | %16f\n", $x, $f->($x);
    }
}

my $pi = 4 * atan2(1,1);

sub menu {
    my $points = -1 + prompt("Create a spline of sin(x) with how many points? ", '-num');
    print "Building spline...";
    my $spline = spline_from_function(0, $pi, $points, sub { sin($_) });
    print "Done\n";

    my %code = (
        'point' => sub {
            my $x = prompt("  x = ", '-num');
            my $sin = sin($x);
            my $spl = $spline->($x);
            my $err = abs($sin - $spl);
            print <<END;
  sin(x)    = $sin
  spline(x) = $spl
  error(x)  = $err
END
        },
        'table' => sub {
            my $n = -1 + prompt("  number of samples = ", '-integer');
            spline_table(0, $pi, $n, $spline);
        },
    );

    my $r = prompt(-menu => { 'Sample the spline at a point' => 'point', 
                              'Print a table of samples' => 'table' });
    $code{$r}->();
}

do {
    menu();
} while (prompt "Again? ", '-yn');
