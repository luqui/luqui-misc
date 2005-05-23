package Grid;

use strict;
use warnings;

use Glop;
use Glop::AutoGL;
use Perl6::Attributes;

sub new {
    my ($self, $ll, $ur, $spacing) = @_;
    bless {
        ll => $ll,
        ur => $ur,
        spacing => $spacing,
    } => ref $self || $self;
}

sub draw {
    my ($self) = @_;
    $.drawing ||= drawing {
        glColor(0.3, 0.3, 0.3);
        glBegin(GL_LINES);
        for (my $x = $.ll->x; $x <= $.ur->x; $x += $.spacing->x) {
            glVertex($x, $.ll->y);
            glVertex($x, $.ur->y);
        }
        for (my $y = $.ll->y; $y <= $.ur->y; $y += $.spacing->y) {
            glVertex($.ll->x, $y);
            glVertex($.ur->x, $y);
        }
        glEnd();
    };
    $.drawing->draw;
}

1;
