#!/usr/bin/perl

use strict;

use FindBin;
use lib glob "$FindBin::Bin/../blib/{lib,arch}";

use Glop qw{-quiet -fullscreen},
         -view => [ 0, 0, 32, 24 ],
;
use ODE;
use Glop::AutoGL;

my $world = ODE::World->new;
my $contacts = ODE::JointGroup->new;
my $cspace = ODE::Geom::Space::Simple->new;
my $plane = ODE::Geom::Plane->new($cspace,  v(0, 0, 0), v(0, 1, 0));
my $plane2 = ODE::Geom::Plane->new($cspace, v(0, 0, 0), v(1, 0, 0));
my $plane3 = ODE::Geom::Plane->new($cspace, v(32, 0, 0), v(-1, 0, 0));
my $plane4 = ODE::Geom::Plane->new($cspace, v(0, 24, 0), v(0, -1, 0));

sub near {
    my ($ga, $gb) = @_;
    if ($ga->is_space || $gb->is_space) {
        $ga->multi_collide($gb, \&near);
    }
    elsif (my @points = $ga->collide($gb)) {
        for my $point (@points) {
            my $j = ODE::Joint::Contact->new($world, $contacts, {
                mode => [ qw{ Bounce } ],
                pos => $point->pos,
                normal => $point->normal,
                depth => $point->depth,
                bounce => 0.6,
                mu => 1000,
            });
            $j->attach($ga->body, $gb->body);
        }
    }
}

$world->gravity(v(0,-4,0));

for (v(4, 4), v(28, 8), v(8, 12), v(16, 20)) {
    $Glop::KERNEL->add(Block->new($_));
}

my $ball = Ball->new(v(16, 12));
$Glop::KERNEL->add($ball);

$Glop::KERNEL->run(sub {
    $cspace->space_collide(\&near);
    $world->quickstep(STEP);
    $contacts->empty;
});

package Ball;

use Glop;
use Class::Closure;

sub CLASS {
    my $speed = 0;
    my $force = 0;
    
    my $body = $world->new_body;
    my $geom = ODE::Geom::Sphere->new($cspace, 1);
    my $motor = ODE::Joint::AngularMotor->new($world);
    $motor->attach($body, undef);
    $motor->num_axes(1);
    $motor->axis(0, 0, v(0,0,1));
    $body->position($_[1]);
    $body->mass(ODE::Mass->new(1));
    
    $geom->body($body);

    my $update = sub {
        $motor->set_params(Vel => $speed, FMax => $force);
    };
    
    method BUILD => sub {
        Glop::Input->Key(
            '-keydown', right => sub { $speed -= 5; $force += 10; $update->() },
            '-keyup',   right => sub { $speed += 5; $force -= 10; $update->() },
            '-keydown', left  => sub { $speed += 5; $force += 10; $update->() },
            '-keyup',   left  => sub { $speed -= 5; $force -= 10; $update->() },
            '-keydown', down  => sub { $force += 10;              $update->() },
            '-keyup',   down  => sub { $force -= 10;              $update->() },
            '-keydown', up    => sub { $body->add_force(STEP ** -1 * v(0, 10, 0)) },
        );
    };

    destroy {
        print $body->position, "\n";
    };

    method step => sub { };
    method draw => sub {
        preserve {
            glTranslate($body->position->list);
            glRotate(180 / 3.14159 * $body->rotation->angle, $body->rotation->axis->list);
            glColor(1,1,1);
            Glop::Draw->Circle;
            glColor(0,0,0);
            glBegin(GL_LINES);
                glVertex(0,0);
                glVertex(1,0);
            glEnd();
        };
    };

    method keep => sub { $geom && $motor };
}

package Block;

use Glop;
use Class::Closure;

sub CLASS {
    my ($class, $pos) = @_;
    my $geom = ODE::Geom::Box->new($cspace, 2*v(4,1,1));
    $geom->position($pos);

    method keep => sub { $geom };

    method draw => sub {
        preserve {
            glTranslate(@$pos);
            glScale(8,2,2);
            glColor(1,1,1);
            Glop::Draw->Rect;
        };
    };

    method step => sub { };
}
