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
    $self;
}

sub step {
    my ($self) = @_;
    if ($self->{pos}->x < 10) {
        $self->{pos} += STEP * v(1,0);
    }
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glColor(1,1,1);
        Glop::Draw->Circle;
    };
}
