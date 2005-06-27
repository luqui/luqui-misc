#!/usr/bin/perl

use site;
use Glop qw{-fullscreen},
         -view => [ 0, -3, 8, 3 ];

Glop::Agent->InputBox( enter => sub {
    print "You entered '$_[0]'\n";
    $KERNEL->quit;
});

$KERNEL->run;
