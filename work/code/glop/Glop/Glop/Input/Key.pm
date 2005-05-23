package Glop::Input::Key;

use strict;

use Glop ();
use Glop::Input::Backend::SDL;
use Carp;

use base 'Glop::Floater';

sub init {
    my ($self) = @_;
    $self->{event_handlers} = { };

    my $input = Glop::Input::Backend::SDL->get;
    $input->add_handler(SDL::Event::SDL_KEYUP(), sub { $self->handle(@_) });
    $input->add_handler(SDL::Event::SDL_KEYDOWN(), sub { $self->handle(@_) });
}

sub handle {
    my ($self, $e) = @_;
    if ($self->{event_handlers}{$e->key_sym}) {
        $self->{event_handlers}{$e->key_sym}->($e);
    }
    1;
}

sub register {
    my $self = shift;
    $self = $self->make unless ref $self;

    my $state = '-keydown';
    my $chain = undef;
    my %chained;

    while (@_) {
        my $key = shift;
        if (lc $key eq '-keydown' || lc $key eq '-keyup' || lc $key eq '-key') {
            $state = lc $key;
        }
        elsif (lc $key eq '-chain') {
            $chain = 1;
        }
        elsif (lc $key eq '-nochain') {
            $chain = 0;
        }
        elsif ($key =~ /^-/) {
            croak "Unknown option '$key'";
        }
        else {
            no strict 'refs';
            
            $key = uc $key;
            if ($key =~ /^[A-Z]$/) { $key = lc $key }
            my $code = shift;
            my $keycode = "SDL::Event::SDLK_$key"->();
            my $pcode;
            if (defined $chain) {
                $pcode = $chain ? $self->{event_handlers}{$keycode} : undef;
            }
            else {
                $pcode = $chained{$keycode} ? $self->{event_handlers}{$keycode} : undef;
            }
            $chained{$keycode} = 1;

            if ($state eq '-keydown') {
                $self->{event_handlers}{"SDL::Event::SDLK_$key"->()} = sub {
                    my $e = shift;
                    $code->($e->key_name) if $e->type == SDL::Event::SDL_KEYDOWN();
                    $pcode->($e) if $pcode;
                }
            } 
            elsif ($state eq '-keyup') {
                $self->{event_handlers}{"SDL::Event::SDLK_$key"->()} = sub {
                    my $e = shift;
                    $code->($e->key_name) if $e->type == SDL::Event::SDL_KEYUP();
                    $pcode->($e) if $pcode;
                }
            }
            elsif ($state eq '-key') {
                $self->{event_handlers}{"SDL::Event::SDLK_$key"->()} = sub {
                    my $e = shift;
                    my $type = $e->type == SDL::Event::SDL_KEYDOWN() ?
                                  'down' : 'up';
                    $code->($e->key_name, $type);
                    $pcode->($e) if $pcode;
                }
            }
        }
    }
    $self;
}

1;
