#!/usr/bin/perl

my ($eps, $pow) = (1, 0);
while (1) {
    my $diff = (1 + $eps) - 1;
    print "(1 + 2^$pow) - 1 = $diff\n";
    last if $diff == 0;

    $eps /= 2;  $pow--;
}

print "Looks like the number for which underflow occurs is 2^$pow = $eps.\n";
print "Man, that took FOREVER!  I really need to find a faster language. :-)\n";
