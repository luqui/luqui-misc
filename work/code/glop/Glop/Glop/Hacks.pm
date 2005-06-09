package Glop::Hacks;

use strict;
use warnings;
use SDL;

my %missing = (
    'SDL::Event::SDL_BUTTON_LEFT' => sub () { 1 },
    'SDL::Event::SDL_BUTTON_MIDDLE' => sub () { 2 },
    'SDL::Event::SDL_BUTTON_RIGHT' => sub () { 3 },
    'SDL::Event::SDL_BUTTON_WHEELUP' => sub () { 4 },
    'SDL::Event::SDL_BUTTON_WHEELDOWN' => sub () { 5 },
);

for my $func (keys %missing) {
    no strict 'refs';
    unless (exists &$func) {
        *$func = $missing{$func};
    }
}

*::TEXT_SHADED = \&SDL::Event::TEXT_SHADED;

1;
