package Glop::Draw::Circle;

use strict;

use Glop -export => [ 'invar' ];

my $PI = 4 * atan2(1,1);

sub draw_u24 {
    invar {
        package Glop::GLSpace;
        glBegin(GL_TRIANGLE_FAN);
        glVertex(0,0);
        for (my $th = 0; $th <= 2 * $PI; $th += 2 * $PI / 24) {
            glVertex(cos($th), sin($th));
        }
        glEnd();
    };
}

sub draw {
    goto &draw_u24 unless @_ > 1;   # Cached common case
    
    package Glop::GLSpace;
    
    my %opt = @_[1..$#_];
    if (exists $opt{-radius}) {
        glPushMatrix();
        glScale($opt{-radius}, $opt{-radius}, 1);
    }

    my $sides = $opt{-sides} || 24;
    
    if ($opt{-outline}) {
        glBegin(GL_LINE_STRIP);
    }
    else {
        glBegin(GL_TRIANGLE_FAN);
        glVertex(0,0);
    }
            
    for (my $i = 0; $i <= $sides; $i++) {
        glVertex(cos(2 * $PI / $sides * $i), sin(2 * $PI / $sides * $i));
    }

    glEnd();

    if (exists $opt{-radius}) {
        glPopMatrix();
    }
}

1;

=head1 NAME

Glop::Draw::Circle - draw a circle

=head1 SYNOPSIS

    use Glop;

    # Draw a circle in the x-y plane at the origin
    Glop::Draw->Circle(
        -sides => 24,
        -radius => 1,
    );

=head1 DESCRIPTION

Draws a circle centered around the origin in the XY plane.  If the 
C<-radius> option isn't given, the radius defaults to 1.  If the 
C<-sides> option isn't given, uses 24 sides.

=head1 SEE ALSO

L<Glop>
