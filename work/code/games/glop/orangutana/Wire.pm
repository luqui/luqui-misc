package Wire;

use strict;
use Glop;
use Glop::AutoGL;

use base 'Glop::Actor';

sub init {
    my ($self, $mass1, $free1, $mass2, $free2) = @_;

    $mass1->wireinc;
    $mass2->wireinc;

    my $body1;
    if ($free1) {
        $body1 = Glop::Physics->get->world->new_body;
        $body1->position($mass1->position);
        $body1->mass(ODE::Mass->new(0.1));

        $self->{hinge1} = ODE::Joint::Hinge->new(Glop::Physics->get->world);
        $self->{hinge1}->attach($mass1->body, $body1);
        $self->{hinge1}->anchor($mass1->position);
        $self->{hinge1}->axis(v(0,0,1));
    }
    else {
        $body1 = $mass1->body;
    }
    
    my $body2;
    if ($free2) {
        $body2 = Glop::Physics->get->world->new_body;
        $body2->position($mass2->position);
        $body2->mass(ODE::Mass->new(0.1));

        $self->{hinge2} = ODE::Joint::Hinge->new(Glop::Physics->get->world);
        $self->{hinge2}->attach($mass2->body, $body2);
        $self->{hinge2}->anchor($mass2->position);
        $self->{hinge2}->axis(v(0,0,1));
    }
    else {
        $body2 = $mass2->body;
    }

    $self->{slider} = ODE::Joint::Slider->new(Glop::Physics->get->world);
    $self->{slider}->attach($body1, $body2);
    my $axis = $body2->position - $body1->position;
    $self->{slider}->axis($axis);
    $self->{slider}->set_params(LoStop  => 0,
                                HiStop  => 1e999,
                                StopCFM => 0.25,
                                StopERP => 0.01);

    $self->{ext} = $axis->norm;
    $self->{stop} = 0;
    $self->{mass1} = $mass1;
    $self->{mass2} = $mass2;
    $self->{body1} = $body1;
    $self->{body2} = $body2;
}

sub theta {
    my ($self) = @_;
    atan2($self->{body2}->position->y - $self->{body1}->position->y,
          $self->{body2}->position->x - $self->{body1}->position->x);
}

sub control {
    my ($self, $amt) = @_;
    $self->{stop} += $amt;
    if ($self->{stop} > $self->{ext}) {
        $self->{stop} = $self->{ext};
    }
    $self->{slider}->set_params(LoStop => $self->{stop});
    $self->{green} = 1;
}

sub detach {
    my ($self) = @_;
    $self->{slider}->destroy;
    $self->{hinge1} and $self->{hinge1}->destroy;
    $self->{hinge2} and $self->{hinge2}->destroy;
    #$self->{mass1} != $self->{body1} and $self->{body1}->destroy;
    #$self->{mass2} != $self->{body2} and $self->{body2}->destroy;
    $self->{mass1}->wiredec;
    $self->{mass2}->wiredec;
    $self->kill;
}

sub draw {
    my ($self) = @_;

    if ($self->{green}) {
        glColor(0, 1, 0);
    }
    else {
        glColor(0.8,0.8,0.8);
    }
    my $ext = $self->{slider}->extension;
    my $stop = $self->{stop};
    glLineWidth(3 - 3 / (exp(($stop - $ext)/10) + 1));
    glBegin(GL_LINES);
        glVertex($self->{body1}->position->list);
        glVertex($self->{body2}->position->list);
    glEnd();

    $self->{green} = 0;
}

1;
