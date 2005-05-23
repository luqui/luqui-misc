package Glop::Floater::Timer;

use strict;
use base 'Glop::Floater';
use Glop ();

sub init {
    my ($self, $time, $code) = @_;
    $self->{time}  = $time;
    $self->{code}  = $code;
}

sub step {
    my ($self) = @_;
   
    $self->{time} -= Glop::STEP();
    if ($self->{time} < 0) {
        $self->{code}->();
        $self->kill;
    }
}

1;
