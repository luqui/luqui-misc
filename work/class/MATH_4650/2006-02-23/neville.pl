#!/usr/bin/perl

use Term::ReadLine;

sub neville {
    my ($p) = @_;
    my ($xs, $fs, $Q, %Qcache);
    $xs = [];  $fs = [];
    $Q = sub {
        my ($i, $j) = @_;
        return $fs->[$i] if $j == 0;
        return $Qcache{$i}{$j} if exists $Qcache{$i}{$j};
        
        $Qcache{$i}{$j} = 
            (($p - $xs->[$i-$j]) * $Q->($i, $j-1) - 
             ($p - $xs->[$i])    * $Q->($i-1, $j-1))
                    / ($xs->[$i] - $xs->[$i-$j]);
    };

    return sub {
        my ($x, $fx) = @_;
        push @$xs, $x;
        push @$fs, $fx;
        my $n = @$xs-1;
        return $Q->($n,$n);
    };
}

my $term = Term::ReadLine->new;
my $point = $term->readline('At what point would you like the function evaluated? ');
my $nev = neville($point);

while (defined(my $line = $term->readline('Enter the next point x,f(x): '))) {
    my ($x, $fx) = split /\s*,\s*/, $line;
    print $nev->($x,$fx), "\n";
}
