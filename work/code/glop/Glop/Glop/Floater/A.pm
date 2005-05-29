package Glop::Floater::A;

# It's named as such so you can say:
# A Glop::Floater sub { ... }

use strict;
use Glop ();
use base 'Glop::Floater';
use Carp;

sub init {
    my $self = shift;
    my $arg = $_[0];
    if (ref $arg) {
        if (ref $_[0] eq 'CODE') {
            $self->{draw} = $arg;
        }
        else {
            if ($arg->can('draw')) {
                $self->{draw} = sub { $arg->draw };
            }
            if ($arg->can('step')) {
                $self->{step} = sub { $arg->step };
            }
        }
    }
    else {
        my %arg = @_;
        for (keys %arg) {
            unless ($_ eq 'step' || $_ eq 'draw') {
                confess "Floater::A accepts only the keys 'step' and 'draw', not $_";
            }
            @$self{qw{step draw}} = @arg{qw{step draw}};
        }
    }
}

sub step {
    FLOATER: for ($_[0]) {
        $_[0]->{step} && $_[0]->{step}->($_);
        return;
    }
    $Glop::KERNEL->remove($_[0]);   # if you say "last FLOATER" this is called
}

sub draw {
    FLOATER: for ($_[0]) {
        $_[0]->{draw} && $_[0]->{draw}->($_);
        return;
    }
    $Glop::KERNEL->remove($_[0]);
}

1;
