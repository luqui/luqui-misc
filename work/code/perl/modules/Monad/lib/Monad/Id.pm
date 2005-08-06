package Monad::Id;

use strict;
use warnings;
no warnings 'uninitialized';

sub new {
    my ($class, @vals) = @_;
    bless \@vals => ref $class || $class;
}

sub BIND {
    my ($self, $fn) = @_;
    $fn->(@$self);
}

sub RETURN {
    my ($class, @rest) = @_;
    $class->new(@rest);
}

sub get {
    my ($self) = @_;
    wantarray ? @$self : $self->[0];
}

1;
