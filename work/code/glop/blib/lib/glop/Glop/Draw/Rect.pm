package Glop::Draw::Rect;

use strict;
use Glop ();

sub draw_unit {
    package Glop::GLSpace;
    glBegin(GL_QUADS);
        glVertex(-0.5, -0.5);
        glVertex( 0.5, -0.5);
        glVertex( 0.5,  0.5);
        glVertex(-0.5,  0.5);
    glEnd();
}
    

sub draw {
    goto &draw_unit unless @_ > 1;
    my ($class, $p, $q) = @_;

    package Glop::GLSpace;

    if (defined $p && !defined $q) {
        glPushMatrix();
        glScale(@$p[0,1], 1);
        Glop::Draw::Rect->draw_unit;
        glPopMatrix();
    }
    else {  # defined($p & $q)
        glBegin(GL_QUADS);
            glVertex($p->x, $p->y);
            glVertex($p->x, $q->y);
            glVertex($q->x, $q->y);
            glVertex($q->x, $p->y);
        glEnd();
    }
}

1;

=head1 TITLE

Glop::Draw::Rect - draw a rectangle

=head1 SYNOPSIS

    # centered unit square
    Glop::Draw->Rect;

    # centered rect, side lengths $x, $y
    Glop::Draw->Rect(v($x, $y)); 

    # rect from $u to $v   ($u and $v are vectors)
    Glop::Draw->Rect($u, $v);

=head1 DESCRIPTION

Draws a flat rectangle in the XY plane.  It can be used in any of the
ways shown in the synopsis above.  All arguments should be Glop vectors.
Any z component of such vectors is ignored.

=head1 SEE ALSO

L<Glop>
