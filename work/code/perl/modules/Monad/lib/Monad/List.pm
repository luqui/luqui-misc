package Monad::List;

use strict;
use warnings;
no warnings 'uninitialized';

sub BIND {
    my ($self, $fn) = @_;
    __PACKAGE__->RETURN(map { @{$fn->($_)} } @$self);
}

sub RETURN {
    my ($class, @values) = @_;
    bless \@values => ref $class || $class;
}

sub values {
    my ($self) = @_;
    @$self;
}

1;
