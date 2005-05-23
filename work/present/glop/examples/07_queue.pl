#!/usr/bin/perl

use strict;

use site;
use Glop;

view(-16, -12, 16, 12);

MoveBall->make->actloop;

$KERNEL->run;

package MoveBall;

use base 'Glop::Actor';
use Glop;
use Glop::AutoGL;
use Glop::TransientQueue;

sub new {
    my ($class) = @_;
    my $self = $class->SUPER::new;
    $self->{pos} = v(0,0);
    $self->{queue} = Glop::TransientQueue->new;
    $self;
}

sub move {
    my ($self, $dir) = @_;
    $self->{queue}->push(Timed Glop::Transient 1 => sub {
                $self->{pos} += 4*STEP * $dir;
    });
}

sub actloop {
    my ($self) = @_;
    $self->move(v(1,0));
    $self->move(v(0,1));
    $self->move(v(-1,0));
    $self->move(v(0,-1));
    $self->{queue}->push(sub { $self->actloop(); 0 });
}

sub step {
    my ($self) = @_;
    $self->{queue}->run;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glColor(1,1,1);
        Glop::Draw->Circle;
    };
}
