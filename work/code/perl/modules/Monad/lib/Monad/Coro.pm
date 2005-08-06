package Monad::Coro;

use strict;
use warnings;
no warnings 'uninitialized';

use Exporter;
use base 'Exporter';

our @EXPORT = qw<yield>;

sub yield {
    Monad::Yield->RETURN(@_);
}

sub new {
    my ($self, $code) = @_;
    bless {
        cont => $code,
    } => ref $self || $self;
}

sub start {
    my ($self, @args) = @_;
    $self->{cont} = $self->{cont}->(@args);
    $self->{cont} && $self->{cont}->get;
}

sub next {
    my ($self, @args) = @_;
    $self->{cont} = $self->{cont}->next(@args);
    $self->{cont} && $self->{cont}->get;
}

sub done {
    my ($self) = @_;
    ! $self->{cont};
}

package Monad::Yield;

sub RETURN {
    my ($class, @values) = @_;
    bless {
        values => \@values,
    } => ref $class || $class;
}

sub BIND {
    my ($self, $f) = @_;
    bless {
        cont => $f,
        values => $self->{values},
    } => ref $self;
}

sub next {
    my ($self, @args) = @_;
    $self->{cont}->(@args);
}

sub get {
    my ($self) = @_;
    wantarray ? @{$self->{values}} : $self->{values}[0];
}

1;
