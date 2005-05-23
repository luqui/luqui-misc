package Mass;

use strict;
use Glop;
use Glop::AutoGL;

use base 'Glop::Actor';

sub init {
    my ($self, $pos, $mass, $radius, $color, $sticky, $unstickable, $image) = @_;
    $radius ||= 1;
    Glop::Role->Body($self);
    $self->position($pos);
    $self->body->mass(ODE::Mass->new($mass));

    Glop::Role->Geom($self, [ Sphere => $radius ]);

    $self->{mass} = $mass;
    $self->{pj} = ODE::Joint::Plane2D->new(Glop::Physics->get->world, undef);
    $self->{pj}->attach($self->body, undef);
    $self->{color} = $color || [1,1,1];
    $self->{radius} = $radius;
    $self->{sticky} = $sticky;
    $self->{unstickable} = $unstickable;
    $self->{image} = $image;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->position->list);
        my $q = $self->rotation;
        glRotate($q->angle * 180 / 3.1415, $q->axis->list);
        if ($self->{image}) {
            glColor(1,1,1);
            glScale(2*$self->{radius}, 2*$self->{radius}, 1);
            Glop::Draw->Sprite($self->{image});
        }
        else {
            glColor(@{$self->{color}});
            Glop::Draw->Circle(-radius => $self->{radius});
        }
    };
}

sub wireinc {
    my ($self) = @_;
    $self->{wirecount}++;
}

sub wiredec {
    my ($self) = @_;
    $self->{wirecount}--;
}

sub wirecount {
    my ($self) = @_;
    $self->{wirecount};
}

sub unstickable {
    my ($self) = @_;
    $self->{unstickable};
}

sub sticky {
    my ($self) = @_;
    $self->{sticky};
}

sub stick {
    my ($self, $j) = @_;
    $self->{sticky} = 0;
    $self->{joint} = $j;
}

sub unstick {
    my ($self) = @_;
    $self->{joint}->attach(undef, undef);
    undef $self->{joint};
}

sub stuck {
    my ($self) = @_;
    ! !$self->{joint};
}

sub DESTROY {
    my ($self) = @_;
    delete $::STICKY{$self->body};
}

1;
