package Frame;

use strict;
use warnings;

use Glop;
use Perl6::Attributes;

sub new {
    my ($class, $x, $t) = @_;
    bless { x => $x, t => $t } => ref $class || $class;
}

sub position {
    my ($self) = @_;
    $.x;
}

sub time {
    my ($self) = @_;
    $.t;
}

1;
