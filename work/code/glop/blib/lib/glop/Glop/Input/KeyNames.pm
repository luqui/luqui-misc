package Glop::Input::KeyNames;

use strict;
use Glop ();
use Glop::Input::Backend::SDL;

use base 'Glop::Floater';

sub init {
    my ($self) = @_;

    my $input = Glop::Input::Backend::SDL->get;
    $input->add_handler(SDL::Event::SDL_KEYDOWN(), sub { $self->handle(@_) });
}

my %shiftmap = (
    '`' => '~',
    '1' => '!',
    '2' => '@',
    '3' => '#',
    '4' => '$',
    '5' => '%',
    '6' => '^',
    '7' => '&',
    '8' => '*',
    '9' => '(',
    '0' => ')',
    '-' => '_',
    '=' => '+',
    '\\' => '|',
    '[' => '{',
    ']' => '}',
    "'" => '"',
    ',' => '<',
    '.' => '>',
    '/' => '?',
);

sub handle {
    my ($self, $e) = @_;
    my $name = $e->key_name;
    if (length($name) == 1 && 
        $e->key_mod & SDL::Event::KMOD_SHIFT()) {
            $name = uc $name;
            $name = $shiftmap{$name} || $name;
    }
    $self->{callback}->($name, $e);
}

sub register {
    my ($self, $callback) = @_;
    $self = $self->make;
    $self->{callback} = $callback;
}

1;
