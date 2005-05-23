package Block;

use strict;
use Glop;
use Glop::AutoGL;

use base 'Glop::Actor';

sub init {
    my ($self, $pos, $width, $height) = @_;

    Glop::Role->Geom($self, [ Box => v($width, $height, 1) ]);
    $self->geom->position($pos);
    $self->geom->category_bits(0x1);
    $self->geom->collide_bits(~0x1);

    $self->{width}  = $width;
    $self->{height} = $height;
    $self->{dlist}  = undef;
    $self->{theta}  = rand() * 3.14159 * 2;
}

sub draw {
    my ($self) = @_;
    unless ($self->{dlist}) {
        $self->{dlist} = drawing {
            glColor(1,1,1);
            glScale($self->{width}, $self->{height}, 1);
            Glop::Draw->Sprite("images/block_ice.png");
        };
    }
    else {
        preserve {
            glTranslate($self->geom->position->list);
            $self->{dlist}->draw;
        };
    }
}

1;
