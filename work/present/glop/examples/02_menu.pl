#!/usr/bin/perl

use site;
use Glop;

Glop::Actor->Menu(
    [ 'Start Game' => sub { print "Starting Game\n" } ],
    [ 'End Game'   => sub { $KERNEL->quit } ],
);

$KERNEL->run;
