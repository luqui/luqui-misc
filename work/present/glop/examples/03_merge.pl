#!/usr/bin/perl

use site;
use Glop;

sub menu {
    $KERNEL->new_state;
    Glop::Actor->Menu(
        [ 'Start Game' => sub { circle() } ],
        [ 'End Game'   => sub { $KERNEL->quit } ],
        -size => 72,
    );
}

sub circle {
    $KERNEL->new_state;
    Glop::Actor->Anonymous(
        sub { Glop::Draw->Circle },
    );
    $KERNEL->input->Keyboard->register(
        escape => sub { menu() },
    );
}

menu();

$KERNEL->run;
