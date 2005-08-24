#!/usr/bin/perl

use Math::Big::Factors qw<factors_wheel>;
use List::Util qw<sum>;
use Perl6::Say;
use Data::Histogram;

sub reduction {
    my ($num) = @_;
    sum factors_wheel $num;
}

sub characteristic {
    my ($num) = @_;
    my $new;
    until (($new = reduction $num) == $num) {
        $num = $new;
    }
    $num;
}

print histogram(map { characteristic($_) } 1..1000);
