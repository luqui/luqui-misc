#!/usr/bin/perl

use site;
use Glop;
use Glop::AutoGL;

my $world = ODE::World->new;
$world->gravity(v(0, -1, 0));

sub main_state {
    $KERNEL->new_state;
    view(-16, -12, 16, 12);

    my $body = $world->new_body;
    $body->position(v(0,0));
    Glop::Actor->Anonymous(
        sub { 
            glTranslate($body->position->list);
            Glop::Draw->Circle;
        },
    );
}

main_state();

run $KERNEL sub {
    $world->step(STEP);
};
