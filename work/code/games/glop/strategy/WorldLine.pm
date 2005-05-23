package WorldLine;

use strict;
use warnings;

use Glop ();

sub new {
    my ($class, $init, $time) = @_;
    $time = $::TIME unless defined $time;
    bless [ { time => $time, obj => $init } ] => ref $class || $class;
}

sub add {
    my ($self, $obj, $time) = @_;
    $time = $::TIME unless defined $time;
    push @$self, { time => $time, obj => $obj };
}

sub view {
    my ($self, $frame) = @_;
    my ($x, $t) = ($frame->position, $frame->time);
    for (my $i = 1; $i < @$self; $i++) {
        return if $self->[$i]{time} > $t;
        my $dx = ($self->[$i]{obj}->position - $x)->norm;
        my $cdt = $::C * ($t - $self->[$i]{time});
        if ($dx > $cdt) { return $self->[$i-1]{obj} }
        if ($dx == $cdt) { return $self->[$i]{obj} }
    }
    return;
}

1;
