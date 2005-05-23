#!/usr/bin/perl

use Board;
use strict;
$|=1;

my $board = Board->new;
my $turn = 'X';
my %turn = qw{ X O O X };

while (1) {
    display $board;
    print "$turn\'s turn\n"; 

    my $inp = <>;
    chomp $inp;
    $inp =~ /^([abc])([123])$/i or warn "Invalid input!\n" and redo;
    my ($x, $y) = (ord($1) - ord('a') + 1, $2);

    $board->move($turn, $x, $y);
    $turn = $turn{$turn};

    if (my $win = $board->winner) {
        display $board;
        print "$win wins!\n";
        exit;
    }
}
