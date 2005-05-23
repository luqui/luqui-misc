#!/usr/bin/perl

use lib glob '/home/fibonaci/work/code/glop/blib/{lib,arch}';

use Glop -view => [ -16, -12, 16, 12 ];
use Glop::AutoGL;
use Perl6::Attributes;

use WorldLine;
use Frame;
use Grid;

our $TIME = 0;
our $C = 5;

package Dude;

sub new {
    my ($class, $pos) = @_;
    bless {
        pos => $pos,
    } => ref $class || $class;
}

sub position {
    my ($self) = @_;
    $.pos;
}

package main;

my $dude = Dude->new(v(-16, 0));
my $dudeworld = WorldLine->new($dude);

my $grid = Grid->new(v(-16, -12), v(16, 12), v(1,1));

A Glop::Floater
    step => sub {
        $TIME += STEP;
        $dudeworld->add($dude = Dude->new($dude->position + STEP * v(1, 0)));
    };

A Glop::Floater
    draw => sub {
        my $view = Frame->new(v(0,0), $TIME);
        $grid->draw;
        preserve {
            glTranslate($dude->position->list);
            glColor(1,1,1);
            Glop::Draw->Circle;
        };
        preserve {
            my $mydude = $dudeworld->view($view) or return;
            glTranslate($mydude->position->list);
            glColor(1,0,0);
            Glop::Draw->Circle;
        };
    };

$KERNEL->run;
