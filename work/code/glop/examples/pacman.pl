#!/usr/bin/perl

use strict;

use FindBin;
use lib glob "$FindBin::Bin/../blib/{lib,arch}";

use SDL::App;
use SDL::Event;
use SDL::OpenGL;
use Switch 'Perl6';
use ODE;
use Glop qw{-quiet -fullscreen}, 
          -view => [ 0, 0, 32, 24 ],
          -step => 0.15,
;

my ($WIDTH, $HEIGHT) = (32, 24);
my $PI = 3.1415926536;
my $BADSPEED = 0.5;
my $BLUESECS = 75;
my $LEVELFILE = $ARGV[0] || 'level1.pac';

my $PACMAN;
my @BADDIES;
my $LEVEL;
my $BLUE;

newgame();

my $count = 0;
$KERNEL->run(sub {
    if (++$count % 60 == 0) {
        print "FHz: " . $KERNEL->frame_rate . "\n";
    }
    if ($BLUE) {
        $BLUE -= STEP;
        $BLUE = 0 if $BLUE < 0;
    }
});

sub newgame {
    $KERNEL->new_state;
    $BLUE = 0; @BADDIES = ();
    $LEVEL = Level->new($LEVELFILE); 
    Glop::Input->Key(
            escape   => sub { $KERNEL->quit },
            left     => sub { $PACMAN->turn(v(-1, 0)) },
            right    => sub { $PACMAN->turn(v( 1, 0)) },
            up       => sub { $PACMAN->turn(v( 0, 1)) },
            down     => sub { $PACMAN->turn(v( 0,-1)) },
            space    => sub { newgame() },
    );
    $KERNEL->add($LEVEL, $PACMAN, @BADDIES);
}

sub freezegame {
    $KERNEL->new_state;
    Glop::Input->Key(
            space => sub { newgame() },
    );
}

package PacMan;

use SDL::OpenGL;
use Class::Closure;

use Glop;

sub CLASS {

    public my $position;
    my $direction = v(0,0);
    my $nextdir   = v(0,0);
    my $face      = v(1,0);
    my $radius    = 0.5;
    
    method BUILD => sub {
        (undef, $position) = @_;
    };

    method draw => sub {
        # print "Drawing Pac Man\n";
        preserve {
        
        glTranslate($position->list);
        glScale($radius, $radius, 1);
        glRotate(180 / $PI * atan2($face->y, $face->x), 0, 0, 1);

        glColor(1,1,0);
        Glop::Draw->Circle;

        glColor(0,0,0);
        my $size = (sin(10*SDL::GetTicks()/1000)+1)/4;
        glBegin(GL_TRIANGLES);
            glVertex(0,0);
            glVertex(1,-$size);
            glVertex(1,$size);
        glEnd();
        
        };
    };

    method step => sub {
        my $q = $position - $position->quantize;

        if ($nextdir && ($direction 
                || Glop::within_box($q, v(0.5-STEP, 0.5-STEP), v(0.5+STEP, 0.5+STEP)))) {
                    
            unless ($LEVEL->blocked($radius * $nextdir + $position + $nextdir * STEP)) {
                $position = $position->quantize + v(0.5,0.5);
                $face = $direction = $nextdir;
                $nextdir = v(0,0);
            }
        }
        
        if ($LEVEL->blocked($radius * $direction + $position + $direction * STEP)) {
            $direction = v(0,0);
        }
        $position += STEP * $direction;
        
        $LEVEL->eat($position);
    };

    method turn => sub {
        my ($self, $vec) = @_;
        $nextdir = $vec;
    };
}


package Baddie;

use SDL::OpenGL;
use Class::Closure;
use Glop;

sub CLASS {

    public my $position;
    has(my $direction) = v(0,0);

    method BUILD => sub {
        (undef, $position) = @_;
    };

    method draw => sub {
        # print "Drawing Baddie $_[0]\n";
        preserve {

        glTranslate($position->list);

        if ($BLUE > 10 || $BLUE > 0 && sin($BLUE) > 0) {
            glColor(0,0,1);
        }
        else {
            glColor(0,1,0);
        }
        glScale(1/sqrt(2), 1/sqrt(2), 1);
        glRotate(45, 0, 0, 1);
        Glop::Draw->Rect;
        
        };
    };

    method step => sub {
        my ($self) = @_;
        my $q = $position - $position->quantize;

        my $S = $BADSPEED * STEP;

        if (Glop::within_box($q, v(0.5-$S, 0.5-$S), v(0.5+$S, 0.5+$S))) {
            my ($min, $mindir) = (($BLUE ? 0 : 1e999), v(0,0));
            CANDIDATE:
            for my $p ($position, $position + v(1,0), $position + v(-1,0), 
                                  $position + v(0,1), $position + v(0,-1)) {
                if (my $d = $LEVEL->diffusion($p)) {
                    if ($BLUE ? $d > $min : $d < $min) {
                        for (@BADDIES) {
                            next if $_ == $self;
                            next CANDIDATE if $_->position->quantize == $p->quantize
                                           || $_->position->quantize == $position->quantize
                                              && $_->direction == $p - $position;
                        }
                        $min = $d;
                        $mindir = $p - $position;
                    }
                }
            }
            $direction = $mindir;
        }

        $position += $S * $direction;

        if ($position->quantize == $PACMAN->position->quantize) {
            if ($BLUE) {
                $position = $LEVEL->portal;
            }
            else {
                ::freezegame();
            }
        }
    }

}


package Level;

use SDL::OpenGL;
use Class::Closure;
use Glop;

sub CLASS {

    has my $nspots;
    has my $portal;
    my $diffusion;
    my $data;
    my $spots;
    my $list;
    my $spotlist;
    
    method BUILD => sub {
        my ($self, $file) = @_;
        $self->load($file);
        $self;
    };

    method load => sub {
        my ($self, $file) = @_;
        $data = [];
        $spots = [];
        $nspots = 0;
        @BADDIES = ();
        open my $fh, '<', $file or die "Couldn't open $file: $!";
        my $y = $HEIGHT-1;
        while ($y >= 0 && (local $_ = readline $fh)) {  # XXX: wtf? while (<$fh>) doesn't work
            chomp;
            my $x = 0;
            for (split //) {
                if ($_ eq '.' || $_ eq '*') {
                    $spots->[$x][$y] = $_;
                    $nspots++;
                }
                elsif ($_ eq '@') {
                    $PACMAN = PacMan->new(v($x+0.5, $y+0.5));
                }
                elsif ($_ eq '&') {
                    push @BADDIES, Baddie->new(v($x+0.5, $y+0.5));
                }
                elsif ($_ eq '#') {
                    $data->[$x][$y] = 1;
                }
                elsif ($_ eq '%') {
                    $portal = v($x+0.5, $y+0.5);
                }
                $x++;
            }
            $y--;
        }
    };

    method step => sub { 
        $_[0]->diffuse($PACMAN->position); 
    };

    method draw => sub {
        # print "Drawing Level\n";
        
        my ($self) = @_;

        invar {
            glColor(0,0,1);
            glBegin(GL_QUADS);
            for my $x (0..$WIDTH) {
                for my $y (0..$HEIGHT) {
                    if ($data->[$x][$y]) {
                        glVertex($x,   $y);
                        glVertex($x+1, $y);
                        glVertex($x+1, $y+1);
                        glVertex($x,   $y+1);
                    }
                }
            }
            glEnd();
        };

        glBegin(GL_QUADS);
        for my $x (0..$WIDTH-1) {
            for my $y (0..$HEIGHT-1) {
                DIF: {
                    last DIF unless $diffusion && $diffusion->[$x][$y];
                    glColor($diffusion->[$x][$y]/64, 0, 0);
                    glVertex($x,   $y);
                    glVertex($x+1, $y);
                    glVertex($x+1, $y+1);
                    glVertex($x,   $y+1);
                }

                SPOT: {
                    last SPOT unless $spots->[$x][$y];
                    glColor(1,1,1);
                    my $sz=0.1;
                    if ($spots->[$x][$y] eq '*') { $sz *= 2; }
                    glVertex($x+0.5-$sz,$y+0.5-$sz);
                    glVertex($x+0.5+$sz,$y+0.5-$sz);
                    glVertex($x+0.5+$sz,$y+0.5+$sz);
                    glVertex($x+0.5-$sz,$y+0.5+$sz);
                }
            }
        }
        glEnd();
    };

    method blocked => sub {
        my ($self, $vec) = @_;
        $data->[$vec->x][$vec->y];
    };
    
    method diffuse => sub {
        my ($self, $pos) = @_;
        $diffusion = [];
        my @dq = [int($pos->x), int($pos->y)];

        for my $x (0..$WIDTH-1) {
            for my $y (0..$HEIGHT-1) {
                unless ($data->[$x][$y]) {
                    $diffusion->[$x][$y] = 1e999;
                }
            }
        }
        
        $diffusion->[$dq[0][0]][$dq[0][1]] = 1;

        while (@dq) {
            my $cur = shift @dq;
            my ($x, $y) = @$cur;
            my $amt = $diffusion->[$x][$y]+1;

            if ($x+1 < $WIDTH &&  $amt < $diffusion->[$x+1][$y]) {
                $diffusion->[$x+1][$y] = $amt;
                push @dq, [$x+1, $y];
            }
            if ($x-1 >= 0 &&      $amt < $diffusion->[$x-1][$y]) {
                $diffusion->[$x-1][$y] = $amt;
                push @dq, [$x-1, $y];
            }
            if ($y+1 < $HEIGHT && $amt < $diffusion->[$x][$y+1]) {
                $diffusion->[$x][$y+1] = $amt;
                push @dq, [$x, $y+1];
            }
            if ($y-1 >= 0 &&      $amt < $diffusion->[$x][$y-1]) {
                $diffusion->[$x][$y-1] = $amt;
                push @dq, [$x, $y-1];
            }
        }
    };

    method diffusion => sub {
        $diffusion && $diffusion->[$_[1]->x][$_[1]->y];
    };

    method eat => sub {
        my ($self, $pos) = @_;
        if ($spots->[$pos->x][$pos->y]) {
            if ($spots->[$pos->x][$pos->y] eq '*') {
                $BLUE = $BLUESECS;
            }
            undef $spots->[$pos->x][$pos->y];
            $nspots--;
        }
        if ($nspots == 0) { ::freezegame() }
    };

}
