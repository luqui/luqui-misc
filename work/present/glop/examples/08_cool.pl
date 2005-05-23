#!/usr/bin/perl

use site;
use Glop;
use Glop::AutoGL;

glMatrixMode(GL_PROJECTION);
        gluPerspective(45, 4/3, 1000, 1);
glMatrixMode(GL_MODELVIEW);

my $t = 200;
Glop::Actor->Anonymous(
    draw => sub {
        my $eye = v(-10, 4, $t);
        my $center = v(0, 0, 0);
        my $up = v(sin(0.001 * $t), cos(0.001 * $t), 0);
        gluLookAt(@$eye, @$center, @$up);
    },
    step => sub {
        $t -= 2*STEP;
    },
);

$KERNEL->add(Spinner->new);

$KERNEL->run;

package Spinner;

use Glop;
use base Glop::Actor;

sub new {
    my ($class) = @_;
    bless {
        dtheta => 0.1,
        theta => 0,
        particles => 4000,
        colcy => 50,
        offset => -500,
    } => ref $class || $class;
}

sub step {
    my ($self) = @_;
    $self->{theta} += $self->{dtheta} * $self->{particles}**-1 * STEP;
}

sub draw {
    my ($self) = @_;
    preserve {
        for my $n ($self->{offset}..$self->{particles}+$self->{offset}-1) {
            glColor(0, 0.5+0.5*sin($self->{colcy} * $self->{theta} + 0.05 * $n), 
                       0.5+0.5*sin(2.616*$self->{colcy} * $self->{theta} + 0.05 * $n));
            
            invar {
                glBegin(GL_TRIANGLES);
                
                for ( [-1, -1, 1], [1, -1, 1], [-1, -1, -1], [1, -1, -1],
                      [-1, 1,  1], [1,  1, 1], [-1,  1, -1], [1,  1, -1]) {
                    glVertex($_->[0], 0, 0);
                    glVertex( 0,$_->[1], 0);
                    glVertex( 0, 0, $_->[2]);
                }
            };

            glEnd();

            glRotate(($self->{particles}-$n)*$self->{theta}, -sin(3*3.1415*$n*$self->{particles}**-1), 0, 
                                        -cos(3*3.1415*$n*$self->{particles}**-1));
            glTranslate(0, 2, 0);
        }
    };
}
