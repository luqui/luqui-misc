#!/usr/bin/perl

use strict;

use lib glob '/home/fibonaci/devel/misc/luke/work/code/glop/blib/{lib,arch}';

use Glop -step => 0.01, '-fullscreen';
use Glop::AutoGL;

use Fighter;
use Block;

use Carp qw{confess};
$SIG{__DIE__} = \&confess;

our @BALLS;

SDL::ShowCursor(0);

Glop::Physics->get->callback(sub {
    my ($a, $b) = ($_[0]{obj_a}, $_[0]{obj_b});

    if ($b->can('sticky') && $b->sticky) {
        ($a, $b) = ($b, $a);
    }
    if ($a->can('sticky') && $a->sticky) {
        return 1 if $b->can('unstickable') && $b->unstickable;
        my $joint = ODE::Joint::Hinge->new(Glop::Physics->get->world);
        $joint->attach($a->body, $b->can('body') ? $b->body : undef);
        $joint->axis(v(0,0,1));
        $joint->anchor($a->body->position);

        $a->stick($joint);
        $b->can('stuck') and $b->stuck and $b->unstick;
        0;
    }
    elsif ($a->can('stuck') && $a->stuck || $b->can('stuck') && $b->stuck) {
        0;
    }
    else {
        1;
    }
});

my @plpos = do($ARGV[0] || "levels/random.ora") or die;
my @plcol = qw{red green};

our $player = 0;
our @players;

our $turnno = 0;

for (my $i = 0; $i < @plpos; $i++) {
    push @players, Fighter->make(v(@{$plpos[$i]}), $plcol[$i % @plcol]);
}

A Glop::Floater
    step => sub { 
        glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        my $ll = $players[$player]->position - v($Tweak::viewport_width, $Tweak::viewport_height)/2;
        if ($ll->x < 0) { $ll = v(0, $ll->y) }
        if ($ll->y < 0) { $ll = v($ll->x, 0) }
        if ($ll->x + $Tweak::viewport_width > $Tweak::field_width) {
            $ll = v($Tweak::field_width - $Tweak::viewport_width, $ll->y);
        }
        if ($ll->y + $Tweak::viewport_height > $Tweak::field_height) {
            $ll = v($ll->x, $Tweak::field_height - $Tweak::viewport_height);
        }
        gluOrtho2D($ll->x, $ll->x + $Tweak::viewport_width,
                   $ll->y, $ll->y + $Tweak::viewport_height);
        glMatrixMode(GL_MODELVIEW);
    };

Glop::Physics->get->world->gravity(v(0,-$Tweak::gravity,0));
Glop::Physics->get->suspend;

A Glop::Actor
    init => sub {
        Glop::Role->Geom($_[0], [ Plane => v($Tweak::field_width, 0, 0), v(-1, 0, 0) ]);
    },
    unstickable => sub { 1 },
;
A Glop::Actor
    init => sub {
        Glop::Role->Geom($_[0], [ Plane => v(0, 0, 0), v(1, 0, 0) ]);
    },
    unstickable => sub { 1 },
;
A Glop::Actor
    init => sub {
        Glop::Role->Geom($_[0], [ Plane => v(0, $Tweak::field_height, 0), v(0, -1, 0) ]);
    },
    unstickable => sub { 1 },
;

sub flash {
    glColor(@_);
    Glop::Draw->Rect(v(0,0), v($Tweak::field_width, $Tweak::field_height));
}

our $MOVING;

my $lctrln = 1;
my $returnn = 1;
my $ending = 0;
Glop::Input->Key(
    lctrl  => sub {
        return if !$lctrln || $ending || !$MOVING;
        $lctrln--;  
        flash(1,0,0);
        $ending = 1;
        Timer Glop::Floater 0.1 => sub { 
            flash(1,0,0);
            Timer Glop::Floater 1 => sub { $ending = 0; endturn($turnno) };
        };
    },
    kp_enter => sub { 
        return if !$returnn || $ending || !$MOVING;
        $returnn--; 
        flash(0,1,0);
        $ending = 1;
        Timer Glop::Floater 0.1 => sub { 
            flash(0,1,0);
            Timer Glop::Floater 1 => sub { $ending = 0; endturn($turnno) };
        };
    },
);

sub endturn {
    my ($turn) = @_;
    return unless $MOVING;
    return unless $turnno == $turn;

    $turnno++;
    Glop::Physics->get->suspend;
    $players[$player]->nomove;

    Timer Glop::Floater $Tweak::turn_pause => sub {
        $player++;
        $player %= @players;
        $MOVING = 0;
        Timer Glop::Floater $Tweak::turn_pause => sub {
            nextmove();
        };
    };
}

sub drawtimer {
    my ($turn) = @_;
    
    return if $turn != $turnno;
    glMatrixMode(GL_PROJECTION);
    glPushMatrix();
    glLoadIdentity();
    gluOrtho2D(0, 1, 0, 1);
    glMatrixMode(GL_MODELVIEW);
    glColor(0,0.5,1);
    if ($ending) {
        if (sin(10 * 3.1415 * $_[1]) > 0) {
            Glop::Draw->Rect(v(0,0), v(1,0.01));
        }
    }
    else {
        Glop::Draw->Rect(v(0,0), v($_[1]/$_[2], 0.01));
    }
    glMatrixMode(GL_PROJECTION);
    glPopMatrix();
    glMatrixMode(GL_MODELVIEW);
}

sub startmove {
    return if $MOVING;
    $MOVING = 1;
    Glop::Physics->get->resume;
    my $myturn = $turnno;
    Timer Glop::Floater $Tweak::turn_length => sub { endturn($myturn) };

    Timed Glop::Floater $Tweak::turn_length => sub {
        drawtimer($myturn, @_);
    };
}

sub nextmove {
    for (my $i = 0; $i < @BALLS; $i++) {
        if ($BALLS[$i]->position->y < -1 && $BALLS[$i]->wirecount == 0) {
            $BALLS[$i]->kill;
            splice @BALLS, $i, 1;
            $i--;
        }
    }
    
    $players[$player]->move;
}

nextmove();
    

$KERNEL->run;
