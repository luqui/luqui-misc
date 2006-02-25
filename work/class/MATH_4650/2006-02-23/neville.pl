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

__END__

OUTPUT:

At what point would you like the function evaluated? 3.7
Enter the next point x,f(x): 1,-0.841471
-0.841471
Enter the next point x,f(x): 3.2,1.22152
1.69038159090909
Enter the next point x,f(x): 3.3,1.35167
1.90390276679842
Enter the next point x,f(x): 4,2.1431
1.83698399096556
Enter the next point x,f(x): 0.5,-1.17257
1.84364754217956
Enter the next point x,f(x): 2.1,-0.121272
1.83736920043875

----------

At what point would you like the function evaluated? 3.7
Enter the next point x,f(x): 4,2.1431
2.1431
Enter the next point x,f(x): 0.5,-1.17257
1.85889971428571
Enter the next point x,f(x): 2.1,-0.121272
1.71223544360902
