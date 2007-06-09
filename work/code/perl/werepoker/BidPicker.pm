package BidPicker;

use strict;

sub assign {
    my ($mat, $outvec) = @_;
    @$outvec = @{_assign($mat, [ (undef) x @$mat ])};
}

sub _assign {
    my ($mat, $invec) = @_;

    while (grep { !defined } @$invec) {
        # find the minimum elements
        my @mins;
        {
            my $minval = 1e999;
            for my $i (0..@$mat-1) {
                next if defined $invec->[$i];
                
                for my $j (0..@{$mat->[$i]}) {
                    next if grep { defined && $_ == $j } @$invec;
                    
                    if ($mat->[$i][$j] < $minval) {
                        $minval = $mat->[$i][$j];
                        @mins = ([$i,$j]);
                    }
                    elsif ($mat->[$i][$j] == $minval) {
                        push @mins, [$i,$j];
                    }
                }
            }
        }
        
        my $min = $mins[rand @mins];
        $invec->[$min->[0]] = $min->[1];
    }

    return $invec;
}

1;
