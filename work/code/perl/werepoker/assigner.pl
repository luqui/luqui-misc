#!/usr/bin/perl

use Algorithm::Munkres ();
use Term::ReadLine;
use Data::Dumper;

use strict;

my @roles = (
    'witch',
    'seer',
    'wench',
    'bodyguard',
    'werewolf',
    'werewolf',
    'howler',
    'villager',
    'villager',
    'gamemaster',
);

my @rolenames;
{
    my %t;
    @t{@roles} = ();
    @rolenames = sort keys %t;
}

my $term = Term::ReadLine->new;

my %players;

ADDPLAYERS:
while (1) {
    my $nplayers = keys(%players)+1;
    my $nroles = @roles;
    print "\e[2J\e[1H\n";
    my $name = $term->readline("$nplayers/$nroles: Name ('done' if done): ");
    next unless $name =~ /^\w+$/;
    last if $name eq 'done';

    my $player = { 
        name => $name,
    };
    
    while (1) {
        print "Pick a role to bid on:\n";
        for my $i (0..$#rolenames) {
            print "  $i: $rolenames[$i]\n";
        }
        my $roleno = $term->readline("('done' if done)? ");
        last if $roleno eq 'done';
        next unless $roleno =~ /^\d+$/ && $roleno < @rolenames;
        my $role = $rolenames[$roleno];
        my $bid = $term->readline("How much to bid on $role? ");
        $player->{bids}{$role} = $bid;
    }
    
    $players{$name} = $player;
}

my @players = values %players;

{
    open my $fh, '>', 'LASTGAME';
    print $fh Dumper(\@players);
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
    print "Press enter, gamemaster, whoever you are.\n";
    <STDIN>;
}

print "Here are the role assignments:\n";
for my $i (0..$#players) {
    print "  $players[$i]{name} - $roles[$solution[$i]] - \$$players[$i]{bids}{$roles[$solution[$i]]}\n";
}
<STDIN>;
