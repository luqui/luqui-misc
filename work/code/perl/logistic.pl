#!/usr/bin/perl

my @array = (0) x 10_000;
$array[50] = 1;
my $count = 1;

my $iter = 0;

while ($count < @array) {
    my $n = int rand @array;
    if ($array[$n]) {
        my $m = int rand @array;
        $array[$m] or ++$array[$m] and ++$count;
    }
    print "$iter $count\n";
    $iter++;
}
