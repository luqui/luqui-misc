#!/usr/bin/perl

use strict;
use lib glob '/home/fibonaci/devel/glop/blib/{lib,arch}';
use Glop 
    '-fullscreen',
    -view => [ [ 30, 30, 50 ], [ 16, 12, 0 ], [ 0, 1, 0 ] ],
    -step => 0.01;
use Glop::AutoGL;
use ODE;

my $CFM = 0.05;
my $BASE = v(4, 0.5, 2);
my $HEAD_SIZE = 1;
my $BASE_MASS = 1;
my $HEAD_MASS = 1;

my $world = ODE::World->new;
my $contact_group = ODE::JointGroup->new;

sub near {
    my ($ga, $gb) = @_;
    if ($ga->is_space || $gb->is_space) {
        $ga->multi_collide($gb, \&near);
    }
    elsif (my @points = $ga->collide($gb)) {
        for my $point (@points) {
            my $j = ODE::Joint::Contact->new($world, $contact_group, {
                mode => [ qw{ Bounce } ],
                pos => $point->pos,
                normal => $point->normal,
                depth => $point->depth,
                bounce => 0.2,
                mu => 0.01,
            });
            $j->attach($ga->body, $gb->body);
        }
    }
}

$world->gravity(v(0, -1, 0));

my $collide_space = ODE::Geom::Space::Simple->new;
my $ground_plane  = ODE::Geom::Plane->new($collide_space, v(0, 0, 0), v(0, 1, 0));

my $foot_body = $world->new_body;
my $foot_geom = ODE::Geom::Box->new($collide_space, $BASE);
$foot_body->mass(ODE::Mass->new($BASE_MASS));
$foot_body->position(v(16, 0.25, 0));
$foot_geom->body($foot_body);

my $phi_body = $world->new_body;
$phi_body->mass(ODE::Mass->new(0.1));
$phi_body->position(v(16, 0.25, 0));

my $theta1_body = $world->new_body;
$theta1_body->mass(ODE::Mass->new(0.1));
$theta1_body->position(v(14, 2, 0));

my $theta2_body = $world->new_body;
$theta2_body->mass(ODE::Mass->new(0.1));
$theta2_body->position(v(14, 2, 0));

my $head_body = $world->new_body;
my $head_geom = ODE::Geom::Sphere->new($collide_space, $HEAD_SIZE);
$head_body->mass(ODE::Mass->new($HEAD_MASS));
$head_body->position(v(16, 4, 0));
$head_geom->body($head_body);

my $foot_phi = ODE::Joint::Hinge->new($world);
$foot_phi->attach($foot_body, $phi_body);
$foot_phi->anchor($phi_body->position);
$foot_phi->axis(v(0,0,1));
$foot_phi->set_params(LoStop => 0, HiStop => 0, StopCFM => $CFM);

my $phi_theta1 = ODE::Joint::Slider->new($world);
$phi_theta1->attach($phi_body, $theta1_body);
$phi_theta1->axis($theta1_body->position - $phi_body->position);
{
    my $ext = $phi_theta1->extension;
    $phi_theta1->set_params(LoStop => $ext, HiStop => $ext);
}

my $theta1_theta2 = ODE::Joint::Hinge->new($world);
$theta1_theta2->attach($theta1_body, $theta2_body);
$theta1_theta2->anchor($theta1_body->position);
$theta1_theta2->axis(v(0,0,1));
$theta1_theta2->set_params(LoStop => 0, HiStop => 0, StopCFM => $CFM);

my $theta2_head = ODE::Joint::Slider->new($world);
$theta2_head->attach($theta2_body, $head_body);
$theta2_head->axis($head_body->position - $theta2_body->position);
{
    my $ext = $theta2_head->extension;
    $theta2_head->set_params(LoStop => $ext, HiStop => $ext);
}

A Glop::Floater sub {
    preserve {
        glColor(1,1,1);
        glTranslate($foot_body->position->list);
        glRotate(180 / 3.14159 * $foot_body->rotation->angle, $foot_body->rotation->axis->list);
        my $b = $BASE / 2;
        glBegin(GL_QUADS);
        for ( [ -$b->x, -$b->y, -$b->z ], # back
              [  $b->x, -$b->y, -$b->z ],
              [  $b->x,  $b->y, -$b->z ],
              [ -$b->x,  $b->y, -$b->z ], 
              [ -$b->x, -$b->y,  $b->z ], # front
              [  $b->x, -$b->y,  $b->z ],
              [  $b->x,  $b->y,  $b->z ],
              [ -$b->x,  $b->y,  $b->z ], 
              [ -$b->x, -$b->y, -$b->z ], # bottom
              [  $b->x, -$b->y, -$b->z ],
              [  $b->x, -$b->y,  $b->z ],
              [ -$b->x, -$b->y,  $b->z ], 
              [ -$b->x,  $b->y, -$b->z ], # top
              [  $b->x,  $b->y, -$b->z ],
              [  $b->x,  $b->y,  $b->z ],
              [ -$b->x,  $b->y,  $b->z ], 
              [ -$b->x, -$b->y, -$b->z ], # left
              [ -$b->x,  $b->y, -$b->z ],
              [ -$b->x,  $b->y,  $b->z ],
              [ -$b->x, -$b->y,  $b->z ],
              [  $b->x, -$b->y, -$b->z ], # right
              [  $b->x,  $b->y, -$b->z ],
              [  $b->x,  $b->y,  $b->z ],
              [  $b->x, -$b->y,  $b->z ],
            ) {
                glVertex(@$_);
        }
        glEnd();
    }
};

Glop::Floater->A(sub {
    preserve {
        glColor(1,1,1);
        glTranslate($head_body->position->list);
        Glop::Draw->Circle(-radius => $HEAD_SIZE);
    }
});

Glop::Floater->A(sub {
    my $foot = $foot_body->position;
    my $head = $head_body->position;
    my $mid  = $theta1_body->position;
    glColor(1,1,1);
    glLineWidth(2.0);
    glBegin(GL_LINES);
        glVertex($foot->list);
        glVertex($mid->list);
        glVertex($mid->list);
        glVertex($head->list);
    glEnd();
});

Glop::Floater->A(sub {
    glColor(1,1,1);
    glLineWidth(2.0);
    glBegin(GL_LINES);
        glVertex(0,  0, -16);
        glVertex(32, 0, -16);
        glVertex(32, 0, -16);
        glVertex(32, 0,  16);
        glVertex(32, 0,  16);
        glVertex(0,  0,  16);
        glVertex(0,  0,  16);
        glVertex(0,  0, -16);
    glEnd();
});

my $pos = [ 0, 0 ];

my $time = 0;

sub current {
    my ($pos, $dir) = @_;
    if ($dir > 0) {
        $pos + 20 * STEP;
    } 
    else {
        $pos - 20 * STEP;
    }
}

sub release {
    my ($pos, $dir, $start) = @_;
    if ($time - $start < 0.4) {
        $dir * 20;
    }
    else {
        $pos;
    }
}

my %start;

Glop::Input->Key(
    '-keydown',
        left  => sub { $start{left} = $time },
        right => sub { $start{right} = $time },
        up    => sub { $start{up} = $time },
        down  => sub { $start{down} = $time },
    '-keyup',
        left  => sub { $pos->[0] = release($pos->[0], -1, $start{left}) },
        right => sub { $pos->[0] = release($pos->[0], 1, $start{right}) },
        up    => sub { $pos->[1] = release($pos->[1], -1, $start{up}) },
        down  => sub { $pos->[1] = release($pos->[1], 1, $start{down}) },
);

A Glop::Floater sub {
    Glop::Input->KeyState->left  and $pos->[0] = current($pos->[0], -1);
    Glop::Input->KeyState->right and $pos->[0] = current($pos->[0], 1);
    Glop::Input->KeyState->up    and $pos->[1] = current($pos->[1], -1);
    Glop::Input->KeyState->down  and $pos->[1] = current($pos->[1], 1);
};

Glop::Floater->A(sub {
    $time += STEP;
    my $anglea = 3.14159 / 180 * $pos->[0];
    my $angleb = 3.14159 / 180 * $pos->[1];
    $foot_phi->set_params(LoStop => $anglea-0.1, HiStop => $anglea+0.1);
    $theta1_theta2->set_params(LoStop => $angleb-0.1, HiStop => $angleb+0.1);
});

$KERNEL->run(sub {
    $collide_space->space_collide(\&near);
    $world->quickstep(STEP);
    $contact_group->empty;
});
