package Block;

use strict;
use Glop;
use Glop::AutoGL;

use base 'Glop::Actor';

# XXX: Ack! Cut & Paste!  REFACTOR!

use Class::Multimethods;

multimethod collide => qw(Block Block) => sub {
    { };
};

multimethod collide => qw(Block::AntiNeutrino Block::Neutrino) => sub {
    collide(@_[1,0]);
};

multimethod collide => qw(Block::Neutrino Block::AntiNeutrino) => sub {
    $_[0]->destroyed;
    $_[1]->destroyed;
    undef;
};


package Block::Neutron;

use Glop;
use FindBin;

use base 'Block';

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

my $visc = 0.2;
my $angular_visc = 0.3;

sub new {
    my ($class, $pos) = @_;
    my $body = $GLOBAL{ode_world}->new_body;
    $body->position($pos);
    my $geom = ODE::Geom::Box->new($GLOBAL{collision_space}, v(3.9, 1.9, 1));
    $geom->body($body);

    my $pj = ODE::Joint::Plane2D->new($GLOBAL{ode_world}, undef);
    $pj->attach($body, undef);

    $GLOBAL{blocks}++;
        
    my $self = $class->SUPER::new;
    $self->{body} = $body;
    $self->{geom} = $geom;
    $self->{dtime} = 1e999;
    $self->{planejoint} = $pj;

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{body}->position->list);
        my $q = $self->{body}->rotation;
        glRotate($q->angle * 180 / 3.1415, $q->axis->list);
        if ((my $dtime = $self->{dtime}) < 1) { 
            glEnable(GL_BLEND);
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
            glColor($dtime-0.3, 0.7 * ($dtime-0.3), 0, $dtime-0.3);
            Glop::Draw->Rect(v(3.9, 1.9));

            glDisable(GL_DEPTH_TEST);
            glColor(1, $dtime, $dtime, $dtime);
            Glop::Draw->Circle(-radius => 3*(2-$dtime));
            glEnable(GL_DEPTH_TEST);
            glDisable(GL_BLEND);
        }
        else {
            glColor(1, 1, 1);
            glScale(3.9,1.9,1);
            glEnable(GL_BLEND);
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
            Glop::Draw->Sprite("$FindBin::Bin/images/neutron.png");
            glDisable(GL_BLEND);
        }
    };
}

sub step {
    my ($self) = @_;
    
    if ($self->{body}->velocity->norm > 5) {
        $self->destroyed;
    }
    
    $self->{dtime} -= STEP;
    $self->{body}->add_force(-$visc * $self->{body}->velocity);
    $self->{body}->add_torque(-$angular_visc * $self->{body}->angular_velocity);
    if ($self->{dtime} <= 0) {
        $KERNEL->remove($self);
        $self->{geom}->destroy;    
        $GLOBAL{blocks}--;
    }

    # correct angular drift
    {
        my $v = $self->{body}->angular_velocity;
        $self->{body}->angular_velocity(v(0, 0, $v->z));

        my $q = $self->{body}->rotation;
        $self->{body}->rotation(ODE::Quaternion->new($q->[0], 0, 0, $q->[3]));
    }
}

sub destroyed {
    my ($self) = @_;
    $self->{dtime} = 1 if $self->{dtime} > 1;
}

package Block::Neutrino;

use Glop;

use base 'Block';

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

my $visc = 0.2;
my $angular_visc = 0.3;

sub new {
    my ($class, $pos) = @_;
    my $body = $GLOBAL{ode_world}->new_body;
    $body->position($pos);
    my $geom = ODE::Geom::Sphere->new($GLOBAL{collision_space}, 1.5);
    $geom->body($body);

    my $pj = ODE::Joint::Plane2D->new($GLOBAL{ode_world}, undef);
    $pj->attach($body, undef);

    $GLOBAL{blocks}++;
        
    my $self = $class->SUPER::new;
    $self->{body} = $body;
    $self->{geom} = $geom;
    $self->{dtime} = 1e999;
    $self->{planejoint} = $pj;

    $GLOBAL{collider}->register($geom => $self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{body}->position->list);
        my $q = $self->{body}->rotation;
        glRotate($q->angle * 180 / 3.1415, $q->axis->list);
        glColor(0.7, 0.7, 0.7);
        if ((my $dtime = $self->{dtime}) < 1) { 
            Glop::Draw->Circle(-radius => 1.5 * $dtime);
        }
        else {
            Glop::Draw->Circle(-radius => 1.5);
        }
    };
}

sub step {
    my ($self) = @_;
    
    $self->{dtime} -= STEP;
    $self->{body}->add_force(-$visc * $self->{body}->velocity);
    $self->{body}->add_torque(-$angular_visc * $self->{body}->angular_velocity);
    if ($self->{dtime} <= 0) {
        $KERNEL->remove($self);
        $self->{geom}->destroy;    
        $GLOBAL{blocks}--;
    }
    
    # correct angular drift
    {
        my $v = $self->{body}->angular_velocity;
        $self->{body}->angular_velocity(v(0, 0, $v->z));

        my $q = $self->{body}->rotation;
        $self->{body}->rotation(ODE::Quaternion->new($q->[0], 0, 0, $q->[3]));
    }
}

sub destroyed {
    my ($self) = @_;
    $self->{dtime} = 1 if $self->{dtime} > 1;
}

package Block::AntiNeutrino;

use Glop;

use base 'Block';

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

my $visc = 0.2;
my $angular_visc = 0.3;

sub new {
    my ($class, $pos) = @_;
    my $body = $GLOBAL{ode_world}->new_body;
    $body->position($pos);
    my $geom = ODE::Geom::Sphere->new($GLOBAL{collision_space}, 1.5);
    $geom->body($body);

    my $pj = ODE::Joint::Plane2D->new($GLOBAL{ode_world}, undef);
    $pj->attach($body, undef);

    $GLOBAL{blocks}++;
        
    my $self = $class->SUPER::new;
    $self->{body} = $body;
    $self->{geom} = $geom;
    $self->{dtime} = 1e999;
    $self->{planejoint} = $pj;
    
    $GLOBAL{collider}->register($geom => $self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{body}->position->list);
        glColor(0, 0, 0);
        if ($self->{dtime} < 1) { 
            Glop::Draw->Circle(-radius => 1.5 * $self->{dtime});
        }
        else {
            Glop::Draw->Circle(-radius => 1.5);
        }
        glColor(1, 1, 1);
        glLineWidth(2.0);
        glBegin(GL_LINE_LOOP);
        my $pi = 4 * atan2(1,1);
        for (my $i = 0; $i < 2*$pi; $i += 2 * $pi / 24) {
            if ((my $dtime = $self->{dtime}) < 1) {
                glVertex(1.5 * $dtime * cos($i), 1.5 * $dtime * sin($i));
            }
            else {
                glVertex(1.5 * cos($i), 1.5 * sin($i));
            }
        }
        glEnd();
    };
}

sub step {
    my ($self) = @_;
    
    $self->{dtime} -= STEP;
    $self->{body}->add_force(-$visc * $self->{body}->velocity);
    $self->{body}->add_torque(-$angular_visc * $self->{body}->angular_velocity);

    if ($self->{dtime} <= 0) {
        $KERNEL->remove($self);
        $self->{geom}->destroy;
        $GLOBAL{blocks}--;
    }
    
    # correct angular drift
    {
        my $v = $self->{body}->angular_velocity;
        $self->{body}->angular_velocity(v(0, 0, $v->z));

        my $q = $self->{body}->rotation;
        $self->{body}->rotation(ODE::Quaternion->new($q->[0], 0, 0, $q->[3]));
    }
}

sub destroyed {
    my ($self) = @_;
    $self->{dtime} = 1 if $self->{dtime} > 1;
}


