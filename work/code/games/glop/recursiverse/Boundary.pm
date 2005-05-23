package Boundary;

use strict;

use Glop;
use Glop::AutoGL;
use Perl6::Attributes;

sub new {
    my ($class, $width, $center, $radius) = @_;
    my $init = {
        center => $center,
        radius => $radius,
    };
    my $self = bless {
        width => $width,
        buf   => [ 
            map { { %$init } } 1..$width,
        ],
        linecounter => 0,
    } => ref $class || $class;

    for (my $i = 0; $i < $width; $i += 10) {
        $.buf[$i]{line} = 1;
    }

    $self;
}

sub width {
    my ($self) = @_;
    $.width;
}

sub advance {
    my ($self, $center, $radius) = @_;
    shift @.buf;
    push @.buf, { center => abs $center, radius => $radius };
    if (++$.linecounter % 10 == 0) {
        $.linecounter = 0;
        $.buf[-1]{line} = 1;
    }
}

sub slice {
    my ($self, $pos) = @_;
    if ($pos < 0 || $pos >= @.buf) { return (0,0) }
    @{$.buf[$pos]}{'center', 'radius'};
}

sub make_image {
    my ($self, $x, $ypos, $radius, $color, $doubled) = @_;
    $.buf[$x]{image} = {
        center => $ypos,
        radius => $radius,
        color  => $color,
        doubled => $doubled,
    };
}

sub image {
    my ($self, $x) = @_;
    $.buf[$x]{image}
}

sub mark_line {
    my ($self) = @_;
    $.buf[-1]{line} = 1;
}

sub line {
    my ($self, $x) = @_;
    $.buf[$x]{line};
}

1;
