#!/usr/bin/perl

use Brain;

my $brain = Brain->new([10, 5, 5]);

my $result = $brain->run([1,0,1,1,0,1,0,0,1,0]);
print "[ @$result ]\n";
