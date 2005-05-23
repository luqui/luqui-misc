package Glop::Draw::Sprite;

use strict;

use Glop ();

my %texcache;

sub draw {
    my ($self, $image) = @_;

    my $tex;   # We have to do this to keep it around until 
               # the end of the scope
    if (ref $image) {
        $image->bind;
    }
    else {
        $tex = $texcache{$image} ||= Glop::Texture->new($image);
        $tex->bind;
    }

    package Glop::GLSpace;
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glBegin(GL_QUADS);
        glTexCoord(0, 0);  glVertex(-0.5, 0.5);    
        glTexCoord(0, 1);  glVertex(-0.5, -0.5);
        glTexCoord(1, 1);  glVertex( 0.5, -0.5);
        glTexCoord(1, 0);  glVertex( 0.5, 0.5);
    glEnd();
    glDisable(GL_BLEND);

    glBindTexture(GL_TEXTURE_2D, 0);
}

1;

=head1 TITLE

Glop::Draw::Sprite - draw a flat image

=head1 SYNOPSIS

    glTranslate($posx, $posy, $posz);
    Glop::Draw->Sprite("images/foo.png");

=head1 DESCRIPTION

Draws a flat image along the current XY plane in the centered unit square
(-1/2,-1/2)-(1/2,1/2).  Use glTranslate/glScale/glRotate to transform the image
to how you need it. Usage:

    Glop::Draw->Sprite("image.png");

Or:

    my $texture = Glop::Texture->new("image.png");
    Glop::Draw->Sprite($texture);

In the former form, the image is cached in memory so that it doesn't have to 
load it from the file every frame if you're drawing this as a sprite.  In the
latter form, no caching is done.

Take note that the image's width and height (as specified in the file) must be
powers of two.  They needn't be the same, however.  You will get a complaint
if it is not.

Supports all formats that Glop::Texture does (it's actually just a thin wrapper
around Glop::Texture).

=head1 SEE ALSO

L<Glop>, L<Glop::Texture>
