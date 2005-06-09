package Glop::Input::Mouse;

use strict;

use Glop ();
use Glop::Input::Backend::SDL;
use Carp;

use base 'Glop::Floater';

sub init {
    my ($self) = @_;
    $self->{event_handlers} = { };

    my $input = Glop::Input::Backend::SDL->get;
    $input->add_handler(SDL::Event::SDL_MOUSEMOTION(),     sub { $self->handle(@_) });
    $input->add_handler(SDL::Event::SDL_MOUSEBUTTONDOWN(), sub { $self->handle(@_) });
    $input->add_handler(SDL::Event::SDL_MOUSEBUTTONUP(),   sub { $self->handle(@_) });
}

sub handle {
    my ($self, $e) = @_;
    if ($e->type == SDL::Event::SDL_MOUSEMOTION()) {
        $self->{event_handlers}{MOTION}->($e);
    }
    else {
        my $idx = $e->button;
        $self->{event_handlers}{$idx} && $self->{event_handlers}{$idx}->($e);
    }
    1;
}

sub register {
    my $self = shift;
    $self = $self->make unless ref $self;

    my $state = '-down';
    my $chain = undef;
    my %chained;

    while (@_) {
        my $key = shift;
        if (lc $key eq '-down' || lc $key eq '-up') {
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
            my $code = shift;
            my $keycode = $key eq 'MOTION' || $key =~ /^\d+$/ ? $key : "SDL::Event::SDL_BUTTON_$key"->();
            my $pcode;
            if (defined $chain) {
                $pcode = $chain ? $self->{event_handlers}{$keycode} : undef;
            }
            else {
                $pcode = $chained{$keycode} ? $self->{event_handlers}{$keycode} : undef;
            }
            $chained{$keycode} = 1;

            if ($key eq 'MOTION') {
                $self->{event_handlers}{$keycode} = sub {
                    my $e = shift;
                    $code->($e->motion_xrel, $e->motion_yrel);
                    $pcode->($e) if $pcode;
                }
            }
            elsif ($state eq '-down') {
                $self->{event_handlers}{$keycode} = sub {
                    my $e = shift;
                    $code->() if $e->type == SDL::Event::SDL_MOUSEBUTTONDOWN();
                    $pcode->($e) if $pcode;
                }
            } 
            elsif ($state eq '-up') {
                $self->{event_handlers}{$keycode} = sub {
                    my $e = shift;
                    $code->() if $e->type == SDL::Event::SDL_MOUSEBUTTONUP();
                    $pcode->($e) if $pcode;
                }
            }
        }
    }
    $self;
}

1;
