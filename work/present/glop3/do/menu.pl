#!/usr/bin/perl

use site;
use Glop;

Glop::Agent->Menu(
    [ 'Start Game' => sub { print "Starting Game\n" } ],
    [ 'End Game'   => sub { $KERNEL->quit } ],
);

$KERNEL->run;
