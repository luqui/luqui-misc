package Glop::Input::KeyState;

use strict;

use Glop ();
use Glop::Input::Backend::SDL;
use SDL::Event ();
use Carp;

my %mods = (
    NUMLOCK  => SDL::Event::KMOD_NUM,
    CAPSLOCK => SDL::Event::KMOD_CAPS,
    LCTRL    => SDL::Event::KMOD_LCTRL,
    RCTRL    => SDL::Event::KMOD_RCTRL,
    CTRL     => SDL::Event::KMOD_CTRL,
    LSHIFT   => SDL::Event::KMOD_LSHIFT,
    RSHIFT   => SDL::Event::KMOD_RSHIFT,
    SHIFT    => SDL::Event::KMOD_SHIFT,
    LALT     => SDL::Event::KMOD_LALT,
    RALT     => SDL::Event::KMOD_RALT,
    ALT      => SDL::Event::KMOD_ALT,
);

sub register {
    __PACKAGE__
}

our $AUTOLOAD;
sub AUTOLOAD {
    no strict 'refs';
    (my $key = $AUTOLOAD) =~ s/.*:://;

    unless ($key =~ /^[a-z]$/i) {
        $key = uc $key;
    }

    if (exists $mods{$key}) {
        ! ! (SDL::GetModState() & $mods{$key});
    }
    else {
        ! ! (SDL::GetKeyState("SDL::Event::SDLK_$key"->()));
    }
}

1;
