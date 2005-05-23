package Glop::Input::Backend::SDL;

use strict;
use Glop ();
use base 'Glop::Floater';
use SDL::Event;

sub get {
    my ($class) = @_;
    $class = ref $class if ref $class;
    $Glop::KERNEL->heap->{"*$class"} ||= $class->make;
}

sub init {
    my ($self) = @_;
    $self->flush;   # flush right when we start so we're not picking 
                    # up 10-second old events
    $self->{handlers} = { };
}

sub flush {
    my ($self) = @_;
    my $e = SDL::Event->new;
    1 while $e->poll;
}

sub step { 
    my ($self) = @_;
    my $e = SDL::Event->new;
    while ($e->poll) {
        my @handlers = (@{$self->{handlers}{ALL}      || []}, 
                        @{$self->{handlers}{$e->type} || []});
        SDL_HANDLER:
        for (@handlers) {
            $_->($e);
        }
    }
}

sub add_handler {
    my ($self, $type, $code) = @_;
    push @{$self->{handlers}{$type}}, $code;
}

1;
