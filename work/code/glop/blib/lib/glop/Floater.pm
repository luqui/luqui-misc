package Glop::Floater;

use Glop ();
use Glop::AutoMethod 'make';

sub new {
    my ($class, @args) = @_;
    bless { } => ref $class || $class;
}

sub init { }

sub make {
    my ($self, @args) = @_;
    $self = $self->new(@args) unless ref $self;
    $self->init(@args);

    $Glop::KERNEL->add($self);
    $self;
}

sub kill {
    my ($self) = @_;
    $Glop::KERNEL->remove($self);
}

sub step { }
sub draw { }

1;
