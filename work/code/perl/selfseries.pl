#!/usr/bin/perl

use List::Util qw< max reduce >;

sub describe {
    my $max = max @_;
    my @ret;
    for my $num (0..$max) {
        my $count = grep { $_ == $num } @_;
        push @ret, $count, $num if $count;
    }
    @ret;
}

sub converge {
    my @seq = @_;
    my %seen;

    for (;;) {
        @seq = describe @seq;
        my $sum = reduce { $a + $b } @seq;
		print "@seq\n";
        my $str = join ';', @seq;
        return $seen{$str} if $seen{$str};
        $seen{$str} = $sum;
    }
}

print converge(@ARGV), "\n";
