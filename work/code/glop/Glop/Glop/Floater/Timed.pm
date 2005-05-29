package Glop::Floater::Timed;

use strict;
use base 'Glop::Floater';
use Glop ();

sub init {
    my ($self, $time, $code) = @_;
    $self->{final} = $time;
    $self->{time}  = 0;
    $self->{code}  = $code;
}

sub step {
    my ($self) = @_;
   
    $self->{time} += Glop::STEP();
    $self->{code}->($self->{time}, $self->{final});
    if ($self->{time} >= $self->{final}) {
        $Glop::KERNEL->remove($self);
    }
}

1;
