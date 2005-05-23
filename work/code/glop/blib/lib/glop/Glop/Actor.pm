package Glop::Actor;

use strict;

use Glop ();
use base 'Glop::Floater';
use Carp;

sub _make_delegate {
    my ($name) = @_;
    sub {
        if (my $m = $_[0]{METHODS}{$name}) {
            goto &$m;
        }
        else {
            no strict 'refs';
            my $mname = "SUPER::$name";
            $_[0]->$mname(@_[1..$#_]);
        }
    };   
}

sub new {
    my $class = shift;
    my $self = $class->SUPER::new(@_);
    $self->{METHODS} = {};
    $self;
}

sub A {
    my ($class, %methods) = @_;
    my $self = $class->new;
    $self->{METHODS}{$_} = $methods{$_} for keys %methods;
    $self->make;
}

sub compose_method {
    my ($self, $name, $code) = @_;
    croak "Role conflict in method '$name'" if $self->{METHODS}{$name};
    $self->{METHODS}{$name} = $code;
}

sub compose_method_chain {
    my ($self, $name, $code) = @_;
    if (my $fcode = $self->{METHODS}{$name}) {
        $self->{METHODS}{$name} = sub { $fcode->(); $code->() };
    }
    else {
        $self->{METHODS}{$name} = $code;
    }
}

BEGIN {
    *init = _make_delegate('init');
    *step = _make_delegate('step');
    *draw = _make_delegate('draw');
}

sub AUTOLOAD {
    our $AUTOLOAD;
    (my $name = $AUTOLOAD) =~ s/.*:://;
    my $code = $_[0]->{METHODS}{$name} 
        or croak "'$name' method not supported " .
                 "(perhaps you didn't implement a role contract?)";
    goto &$code;
}

sub can {
    my ($self, $meth) = @_;
    goto &UNIVERSAL::can unless ref $self;
    $self->{METHODS}{$meth} || UNIVERSAL::can(@_);
}

1;
