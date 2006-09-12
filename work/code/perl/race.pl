#!/usr/bin/perl

use strict;
use Term::ReadLine;
use Lingua::EN::Inflect qw<ORD>;

my $term = Term::ReadLine->new;

my @ACTIONS = ('sharp left turn', 'light left turn', 'straight segment', 'light right turn', 'sharp right turn');

my ($place, $speed, $time) = (5, 5, 30);

my $action = 0;
my $nextaction = int rand 5;
ACTION:
while (1) {
    my $complexity = abs($action - $nextaction);
        
    $action = $nextaction;
    $nextaction = int rand 5;

    if (rand() > $speed / 10) {
        if ($place < 10) {
            $place++;
            print " ** You have been passed.  You are in " . ORD($place) . " place\n";
        }
    }
    if (rand() < $speed / 10) {
        if ($place > 1) {
            $place--;
            print " ** You have passed somebody.  You are in " . ORD($place) . " place\n";
        }
    }

    if ($time == 0) {
        print "The race is over.  You got " . ORD($place) . " place\n";
        last;
    }
    print "You come across a $ACTIONS[$action] followed by a $ACTIONS[$nextaction].\nThere are $time minutes left.\n";
    $time--;
    print "What do you do?\n";
    
    READ:
    $_ = lc $term->readline('? ');
    last if !defined || /quit|exit/;
    while (/\S/) {
        if (s/^\s*speed\s*up//) {
            $speed++; $speed = 10 if $speed > 10;
            print "You speed up to ${speed}0 MPH\n";
            next;
        }
        if (s/^\s*slow\s*down//) {
            $speed--; $speed = 0 if $speed < 0;
            print "You slow down to ${speed}0 MPH\n";
            next;
        }
        if (s/^\s*turn\s*left//) {
            if ($action == 0 && $speed > 9 - $complexity) {
                print "The curve was too sharp.  You slide off the right of the track and die.\n";
                last ACTION;
            }
            if ($action == 0 || $action == 1) {
                print "You turn left.\n";
                next;
            }
            if ($action == 2 || $action == 3 || $action == 4) {
                print "You slide off the right side of the road, ending in a ball of flames.\n";
                last ACTION;
            }
        }
        if (s/^\s*turn\s*right//) {
            if ($action == 4 && $speed > 9 - $complexity) {
                print "The curve was too sharp, and your tires catch the left side of the road and explode.\n";
                last ACTION;
            }
            if ($action == 4 || $action == 3) {
                print "You turn right.\n";
                next;
            }
            if ($action == 2) {
                print "You turn right, just to realize that you had only hallucinated the road turning that way.  You die.\n";
                last ACTION;
            }
            if ($action == 1 || $action == 0) {
                print "You veer off the right of the road screaming 'The other right!  The other right!\n";
                last ACTION;
            }
        }
        if (s/^\s*and//) { next; }
        print "I don't understand '$_'\n";
        goto READ;
    }
}
