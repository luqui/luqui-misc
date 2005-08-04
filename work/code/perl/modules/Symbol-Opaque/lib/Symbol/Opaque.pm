package Symbol::Opaque;

our $VERSION = '0.01';

use 5.006001;
use strict;
use warnings;
use Carp;
use Scalar::Util qw<blessed readonly>;

use overload '<<'  => sub { $_[0]->_op_unify($_[1]) },
             '""'  => sub { $_[0]->string },
;

use Exporter;
use base 'Exporter';

our @EXPORT = qw<sym defsym>;

sub sym {
    my $name = shift;
    Symbol::Opaque->new($name, \(@_));
}

sub defsym {
    my ($name) = @_;
    my $package = caller;
    no strict 'refs';
    my $code = sub { Symbol::Opaque->new($name, \(@_)) };
    *{"$package\::$name"} = $code;
    $code;
}

sub new {
    my ($class, $name, @refs) = @_;
    bless {
        name => $name,
        refs => \@refs,
    } => ref $class || $class;
}

sub _op_unify {
    my ($self, $other) = @_;
    ! !$self->unify($other);
}

sub name {
    my ($self) = @_;
    $self->{name};
}

sub args {
    my ($self) = @_;
    map { $$_ } @{$self->{refs}};
}

sub subunify {
    my ($self, $leftref, $right) = @_;
    if (!defined $$leftref && !readonly $$leftref) {  # a free variable
        $$leftref = $right;
        return sub { undef $$leftref };
    }
    elsif (blessed($$leftref) && $$leftref->isa('Symbol::Opaque')) {
        return $$leftref->unify($right);
    }
    else {
        return $$leftref eq $right ? sub { } : 0;
    }
}

sub unify {
    my ($self, $other) = @_;
    unless (blessed($other) && $other->isa('Symbol::Opaque')) {
        return 0;
    }
    
    my @oargs = $other->args;
    if (@{$self->{refs}} != @oargs) {
        return 0;
    }
    
    my @rollback;
    for my $i (0..$#oargs) {
        my $unif = $self->subunify($self->{refs}[$i], $oargs[$i]);
        if ($unif) {
            push @rollback, $unif;
        }
        else {
            $_->() for @rollback;
            return 0;
        }
    }
    
    return sub { $_->() for @rollback };
}

sub string {
    my ($self) = @_;
    "$self->{name}(" . join(', ', $self->args) . ")";
}

1;
