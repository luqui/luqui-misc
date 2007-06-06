#!/usr/bin/perl

use Algorithm::Munkres ();
use Term::ReadLine;

use strict;

my @roles = (
    ('werewolf') x 2,
    'gamemaster',
);

my @rolenames;
{
    my %t;
    @t{@roles} = ();
    @rolenames = sort keys %t;
}

my $term = Term::ReadLine->new;

my @players;

ADDPLAYERS:
while (1) {
    my $nplayers = @players+1;
    my $nroles = @roles;
    print "\e[2J\e[1H\n";
    my $name = $term->readline("$nplayers/$nroles: Name (blank for done): ");
    last if $name eq '';

    my $player = { 
        name => $name,
    };
    
    while (1) {
        print "Pick a role to bid on:\n";
        for my $i (0..$#rolenames) {
            print "  $i: $rolenames[$i]\n";
        }
        my $roleno = $term->readline('(blank for done)? ');
        last if $roleno eq '';
        my $role = $rolenames[$roleno];
        my $bid = $term->readline("How much to bid on $role? ");
        $player->{bids}{$role} = $bid;
    }
    
    push @players, $player;
}

print "\e[2J";
print "Computing assignment...\n";

# Build matrix.  One row for each player.
my @matrix;
for my $i (0..$#players) {
    for my $j (0..$#roles) {
        $matrix[$i][$j] = -$players[$i]{bids}{$roles[$j]};
    }
}

# Solve system.
my @solution;
Algorithm::Munkres::assign(\@matrix, \@solution);

# Who's the admin?
my $gm;
for my $i (0..$#players) {
    if ($roles[$solution[$i]] eq 'gamemaster') {
        $gm = $players[$i]{name};
        print "The gamemaster is $players[$i]{name}\n";
        print "Gamemaster, press enter to continue.\n";
        <STDIN>;
    }
}

unless (defined $gm) {
    print "Uh, there is no gamemaster in this game\n";
    print "Press enter to add more players\n";
    <STDIN>;
    goto ADDPLAYERS;
}

print "Here are the role assignments:\n";
for my $i (0..$#players) {
    print "  $players[$i]{name} - $roles[$solution[$i]] - \$$players[$i]{bids}{$roles[$solution[$i]]}\n";
}
<STDIN>;
