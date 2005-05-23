#!/usr/bin/perl

use PDL;
use utf8;

# 0,1,2,3
# 2,0,1,3
# 1,2,0,3

sub unop {
    my ($op, $state, $dim, $dims) = @_;
    my @dims = 0..$dims-1;
    unshift @dims, splice @dims, $dim, 1;

    my @backdims = 0..$dims-1;
    splice @backdims, $dim, 0, shift @backdims;

    inner($op, $state->reorder(@dims)->dummy(1))->reorder(@backdims);
}

sub testop {
    my ($state, $dim, $dims) = @_;
    my @dims = 0..$dims-1;
    push @dims, splice @dims, $dim, 1;

    ($state->reorder(@dims)->clump($dims-1)->abs**2)->sumover;
}

my %op = (
    N => pdl(
        [ [ 0, 1 ],
          [ 1, 0 ] ]),

    H => 1/sqrt(2) * pdl(
        [ [ 1, -1 ],
          [ 1, 1 ] ]),
);

my %mop = (
    0 => pdl(
        [ [ 1, 1 ],
          [ 0, 0 ] ]),
    1 => pdl(
        [ [ 0, 0 ],
          [ 1, 1 ] ]),
);

my $v = outer(outer(outer(pdl(1,0), pdl(1,0)), pdl(1,0)), pdl(1,0));

print $v;
while (<>) {
    chomp;
    if (/^([HN])(\d+)$/) {
        $v = unop($op{$1}, $v, $2, 4);
    }
    elsif (/^([T])(\d+)$/) {
        print testop($v, $2, 4);
    }
    elsif (/^([01op])(\d+)$/) {
        $v = unop($mop{$1} * sqrt(testop($v, $2, 4)->at($1)), $v, $2, 4);
    }
    print $v;
}
