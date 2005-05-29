#!/usr/bin/perl

use strict;

use FindBin;
use lib glob "$FindBin::Bin/../blib/{lib,arch}";

use Glop qw{-fullscreen}, 
         -view => [ 0.5, 0, 50, 38 ],
    ;
use Glop::AutoGL;
use PDL;

my ($WIDTH, $HEIGHT) = (51,38);
my $A = 1;
my $HBAR = 1;
my $STEP = 0.20;
my $LATTICE = zeroes(2, $WIDTH, $HEIGHT);
my $POTENTIAL_X = zeroes($WIDTH, $HEIGHT);
my $POTENTIAL_Y = zeroes($WIDTH, $HEIGHT);

for my $x (0..$WIDTH-1) {
    $POTENTIAL_X->slice("$x,:") .= $x / $WIDTH;
}
for my $y (0..$HEIGHT-1) {
    $POTENTIAL_Y->slice(":,$y") .= $y / $HEIGHT;
}

my $sin60 = sin(4*atan2(1,1) / 3);

$LATTICE->set(0, 16,12 => 1); # set (16, 12) = 1 + 0i.

my ($vx, $vy);

Glop::Input->Key(
        left  => sub { $vx += 0.25 },
        right => sub { $vx -= 0.25 },
        down  => sub { $vy -= 0.25 },
        up    => sub { $vy += 0.25 },

        r     => sub { breset() },
        f     => sub { $vx = -$vx;  $vy = -$vy;  $A = -$A; },
        space => sub { collapse() },
    );

sub collapse {
    my $prob = $LATTICE->pow(2)->sumover;
    my $cur = [0,0];
    my $track = 0;
    for my $x (0..$WIDTH-1) {
        for my $y (0..$HEIGHT-1) {
            if (rand($track += $prob->at($x,$y)) < $prob->at($x,$y)) {
                $cur = [$x,$y];
            }
        }
    }
    $LATTICE = zeroes(2, $WIDTH, $HEIGHT);
    $LATTICE->set(0, @$cur => 1);
    print "Total amplitude squared: $track\n";
}

sub breset {
    $LATTICE = zeroes(2, $WIDTH, $HEIGHT);
    $LATTICE->set(0, 16,12 => 1);
    $vx = $vy = 0;
}

sub vampl {
    my ($lattice, $x, $y) = @_;
    
    my $xo = $vx > 0 ? 0 : -$vx;
    my $yo = $vy > 0 ? 0 : -$vy;
    
    $A / 6 * $lattice->slice(":,$x,$y");
#    (($A + $xo + $vx * $POTENTIAL_X->slice("*2,$x,$y") + 
#           $yo + $vy * $POTENTIAL_Y->slice("*2,$x,$y")) * $lattice->slice(":,$x,$y")) / 6;
}

sub e0ampl {
    my ($lattice) = @_;
    
    my $xo = $vx > 0 ? 0 : -$vx;
    my $yo = $vy > 0 ? 0 : -$vy;
    
    (($A + $xo + $vx * $POTENTIAL_X->slice('*2,:,:') + 
           $yo + $vy * $POTENTIAL_Y->slice('*2,:,:')) * $lattice);
}

sub lattice_deriv {
    my ($lattice) = @_;

    my $deriv = e0ampl($lattice);

    # Left/right
    $deriv->slice(':,0:-2,:') -= vampl($lattice, '1:-1',':');
    $deriv->slice(':,1:-1,:') -= vampl($lattice, '0:-2',':');
    # Below, large rows
    $deriv->slice(':,0:-2,2:-1:2') -= vampl($lattice, '0:-2','1:-2:2');
    $deriv->slice(':,1:-1,2:-1:2') -= vampl($lattice, '0:-2','1:-2:2');
    # Below, small rows
    $deriv->slice(':,0:-2,1:-2:2') -= vampl($lattice, '1:-1','0:-3:2');
    $deriv->slice(':,0:-2,1:-2:2') -= vampl($lattice, '0:-2','0:-3:2');
    # Above, large rows
    $deriv->slice(':,0:-2,0:-3:2') -= vampl($lattice, '0:-2','1:-2:2');
    $deriv->slice(':,1:-1,0:-3:2') -= vampl($lattice, '0:-2','1:-2:2');
    # Above, small rows
    $deriv->slice(':,0:-2,1:-2:2') -= vampl($lattice, '1:-1','2:-1:2');
    $deriv->slice(':,0:-2,1:-2:2') -= vampl($lattice, '0:-2','2:-1:2');
    
    my $real = $deriv->slice('0,:,:')->copy;
    $deriv->slice('0,:,:') .= $deriv->slice('1,:,:');
    $deriv->slice('1,:,:') .= -$real;

    $STEP / $HBAR * $deriv;
}

sub compute {
    my $k1 = lattice_deriv($LATTICE);
    my $k2 = lattice_deriv($LATTICE + 0.5 * $k1);
    my $k3 = lattice_deriv($LATTICE + 0.5 * $k2);
    my $k4 = lattice_deriv($LATTICE + $k3);
    $LATTICE += 1/6*$k1 + 1/3*$k2 + 1/3*$k3 + 1/6*$k4;
}

sub draw {
    my @color;
    my $max = 5;
    my $color = $LATTICE->pow(2)->sumover;

    $max = 0.01;

    for (my $y = 0; $y < $HEIGHT-1; $y++) {
        glBegin(GL_TRIANGLE_STRIP);
        for (my $x = 0; $x < $WIDTH; $x++) {
            my $c;
            if ($y % 2 == 0) {   # large row
                $c = $color->at($x,$y) / $max;
                glColor($c,$c,$c);
                glVertex($x,$y);
                $c = $color->at($x,$y+1) / $max;
                glColor($c,$c,$c);
                glVertex($x+0.5,$y+1);
            }
            else {               # small row
                $c = $color->at($x,$y+1) / $max;
                glColor($c,$c,$c);
                glVertex($x,$y+1);
                $c = $color->at($x,$y) / $max;
                glColor($c,$c,$c);
                glVertex($x+0.5,$y);
            }
        }
        glEnd();
    }
}

Glop::Floater->A(sub { compute($vx, $vy) });
Glop::Floater->A(\&draw);

$KERNEL->run;
