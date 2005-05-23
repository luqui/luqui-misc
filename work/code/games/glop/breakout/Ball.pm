# class Ball
package Ball;

use strict;

use Glop;
use Glop::AutoGL;
use FindBin;

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

use base 'Glop::Actor';

use Class::Multimethods;

multimethod collide => qw(Ball Block) => sub { { } };
multimethod collide => qw(Block Ball) => sub { { } };


sub new {
    my ($class, $pos, $vel) = @_;
    my $body = $GLOBAL{ode_world}->new_body;
    $body->position($pos);
    $vel ||= v(0,0);
    $body->velocity($vel);
    my $geom = ODE::Geom::Sphere->new($GLOBAL{collision_space}, 1);
    $geom->body($body);

    my $pj = ODE::Joint::Plane2D->new($GLOBAL{ode_world}, undef);
    $pj->attach($body, undef);

    my $self = $class->SUPER::new;
    $self->{body} = $body;
    $self->{geom} = $geom;
    $self->{planejoint} = $pj;
    
    $GLOBAL{collider}->register($geom => $self);
    $GLOBAL{electrocuter}->add_point($self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{body}->position->list);
        my $q = $self->{body}->rotation;
        glRotate($q->angle * 180 / 3.1415, $q->axis->list);
        glScale(2,2,1);
        glColor(1,1,1);
        glEnable(GL_BLEND);
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
        Glop::Draw->Sprite("$FindBin::Bin/images/electron.png");
        glDisable(GL_BLEND);
    };
}

sub step {
    my ($self) = @_;
    # correct angular drift
    {
        my $v = $self->{body}->angular_velocity;
        $self->{body}->angular_velocity(v(0, 0, $v->z));

        my $q = $self->{body}->rotation;
        $self->{body}->rotation(ODE::Quaternion->new($q->[0], 0, 0, $q->[3]));
    }
}

sub position {
    my ($self) = @_;
    $self->{body}->position;
}

sub apply_field {
    my ($self, $field) = @_;
    $self->{body}->add_force(-200 * $field);
}

1;
