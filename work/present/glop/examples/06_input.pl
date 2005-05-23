#!/usr/bin/perl

use strict;

use site;
use Glop;

view(-16, -12, 16, 12);

MoveBall->make;

$KERNEL->run;

package MoveBall;

use base 'Glop::Actor';
use Glop;
use Glop::AutoGL;

sub new {
    my ($class) = @_;
    my $self = $class->SUPER::new;
    $self->{pos} = v(0,0);
    $self->{dir} = v(0,0);
    $self;
}

sub make {
    my ($self) = @_;
    $self = $self->SUPER::make;
    $KERNEL->input->Keyboard->register(
            left  => sub { $self->{dir} = v(-1,0) },
            right => sub { $self->{dir} = v(1,0) },
            up    => sub { $self->{dir} = v(0,1) },
            down  => sub { $self->{dir} = v(0,-1) },
    );
}

sub step {
    my ($self) = @_;
    $self->{pos} += STEP * $self->{dir};
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glColor(1,1,1);
        Glop::Draw->Circle;
    };
}
