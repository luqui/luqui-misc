#!/usr/bin/perl

use lib glob '/home/fibonaci/devel/misc/luke/work/code/glop/blib/{lib,arch}';
use Glop qw{-fullscreen},
         -view => [ 0, -12, 32, 12 ];

Glop::Agent->InputBox( enter => sub {
    print "You entered '$_[0]'\n";
    $KERNEL->quit;
});

$KERNEL->run;
