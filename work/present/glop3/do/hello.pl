#!/usr/bin/perl

use site;
use Glop;

Glop::Agent->Menu(
    [ "Hello, World" => sub { $KERNEL->quit } ],
);

$KERNEL->run;
