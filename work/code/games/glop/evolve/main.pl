#!/usr/bin/perl

use lib glob '/home/fibonaci/devel/misc/luke/work/code/glop/blib/{lib,arch}';
use Glop '-fullscreen',
          -view => [ 0, 0, 200, 200 ];

use Field;

my $seed;
my $popdata;

if ($ARGV[0]) {
    $seed = $ARGV[0];
    if ($ARGV[1]) {
        open $popdata, '>', $ARGV[1] 
            or die "Couldn't open $ARGV[1] for writing: $!\n";
    }
    else {
        open $popdata, '>', undef;
    }
}
else {
    $seed = int rand ~1;
    open $popdata, '>', "popdata/$seed" 
        or die "Couldn't open popdata/$seed for writing: $!\n";
}
print "$seed\n";
srand $seed;

my $field = Field->new(200, 200);
$field->populate(1000);

A Glop::Floater sub { 
    $field->step; 
    my $pop = $field->population;
    my $food = $field->total_food;
    print $popdata "$pop\t$food\n";
    $KERNEL->quit unless $pop; 
};

run $KERNEL;
