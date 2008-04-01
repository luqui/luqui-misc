#!/usr/bin/perl

# For the git revolution game.  Scans all branches
# in @players and finds the commits which are in a
# majority of the branches, and merges them into 
# the master.

use strict;

my @players = die "Fill in the list of players (and branches)";
my %counts;
my %already;
my %desc;

sub get_commits {
    my ($tag) = @_;
    open my $fh, "git log $tag |";
    my $last;
    my %commits;

    while (<$fh>) {
        if (/^commit ([0-9a-f]+)/) {
            $last = $1;
        }
        $commits{$last} .= $_ if defined $last;
    }
    return %commits;
}

%already = get_commits("heads/master");

foreach my $player (@players) {
    my %commits = get_commits("heads/$player");
    for (keys %commits) {
        push @{$counts{$_}}, $player;
        $desc{$_} ||= $commits{$_};
    }
}

my @merges;
for my $k (keys %counts) {
    if (@{$counts{$k}} > @players/2 && !$already{$k}) {
        print "Supported by @{$counts{$k}}:\n";
        print $desc{$k};
        push @merges, $k;
    }
}

if (@merges) {
    print "git merge @merges\n";
    system "git merge @merges" and die;
}
else {
    print "Nothing to merge.\n";
}
