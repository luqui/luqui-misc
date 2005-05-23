#!/usr/bin/perl

use Carp;

use lib glob '/home/fibonaci/devel/glop/blib/{lib,arch}';
use Glop qw{ -fullscreen },
         -view => [ -32, -24, 32, 24 ];
use Glop::AutoGL;

A Glop::Actor
    init => sub { 
        Glop::Role->Body($_[0]);
        Glop::Role->Geom($_[0], [ Sphere => 1 ]);
    },
    draw => sub {
        my ($self) = @_;
        preserve { 
            glTranslate($self->position->list);
            Glop::Draw->Circle;
        }
    },
;

A Glop::Actor
    init => sub {
        Glop::Role->Geom($_[0], [ Plane => v(0, -24, 0), v(0, 1, 0) ]);
    },
;

Glop::Physics->get->world->gravity(v(0,-9.8,0));

$KERNEL->run;
