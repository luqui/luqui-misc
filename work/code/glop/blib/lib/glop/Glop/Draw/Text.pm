package Glop::Draw::Text;

use strict;

use Glop ();
use SDL::TTFont;
use SDL::Surface;
use Carp;
use POSIX qw{ ceil };

(my $incpath = $INC{'Glop/Draw/Text.pm'}) =~ s/Text\.pm/fonts/;
my %fonts = (
    default  => 'aircut',
    aircut   => "$incpath/aircut3.ttf",
);

sub new {
    my ($package, $text, %opt) = @_;

    my $self = bless { } => ref $package || $package;
    
    if (length($text) == 0) {
        $self->{dontprint} = 1;
        return $self;
    }
    
    $opt{-font} ||= 'default';
    $opt{-size} ||= 24;
    my $font = $opt{-font};

    while ($font !~ /\.ttf$/i) {
        $font = $fonts{$font};
        unless ($font) { croak "Font '$opt{-font}' not found" }
    }

    # perhaps abstract this out into Glop::Font
    my $fobj = SDL::TTFont->new(
        -name => $font,
        -fg   => $SDL::Color::white,
        -bg   => SDL::Color->new(-r => 0, -g => 0, -b => 0),
        -size => $opt{-size},
    ) or confess "Could not create font";

    my $sz = $fobj->width($text);
    my ($orwidth, $orheight);
    if (ref $sz) {       # XXX: Broken method, but we'll handle it when it's fixed, too
        ($orwidth, $orheight) = @$sz;
    }
    else {
        $orwidth = $sz;
        $orheight = $fobj->height;
    }

    $orwidth ||= 2;
    $orheight ||= 2;

    my $pixwidth = 1 << ceil(log($orwidth)/log(2));
    my $pixheight = 1 << ceil(log($orheight)/log(2));
        
    my $surface = SDL::Surface->new(
            -width  => $pixwidth,
            -height => $pixheight,
            -depth  => 32,
    );
    $fobj->print($surface, 0,0, $text);
    
    $self->{width} = $orwidth / $orheight;
    $self->{height} = 1;
    $self->{coordx} = $orwidth / $pixwidth || 1;
    $self->{coordy} = $orheight / $pixheight;

    package Glop::GLSpace;
    glEnable(GL_TEXTURE_2D);
    my ($tex) = @{glGenTextures(1)};
    glBindTexture(GL_TEXTURE_2D, $tex);
    glTexParameter(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameter(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexImage2D(GL_TEXTURE_2D, 0, 4,
                 $pixwidth, $pixheight,
                 0, GL_RGBA, GL_UNSIGNED_BYTE, 
                 $surface->pixels);
    glBindTexture(GL_TEXTURE_2D, 0);
    if (my $error = glGetError()) {
        die gluErrorString($error);
    }

    $self->{tex} = $tex;
                 
    $self;
}

sub DESTROY {
    my ($self) = @_;
    if ($self->{tex}) {
        Glop::GLSpace::glDeleteTextures($self->{tex});
    }
}

sub draw {
    if (ref $_[0]) {      # we're being called as a method
        my $self = shift;

        return if $self->{dontprint};
        
        package Glop::GLSpace;
        glEnable(GL_BLEND);
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
        glBindTexture(GL_TEXTURE_2D, $self->{tex});
        glBegin(GL_QUADS);
            glTexCoord(0, $self->{coordy});
            glVertex(0, 0);
            glTexCoord($self->{coordx}, $self->{coordy});
            glVertex($self->{width}, 0);
            glTexCoord($self->{coordx}, 0); 
            glVertex($self->{width}, $self->{height});
            glTexCoord(0, 0);  
            glVertex(0, $self->{height});
        glEnd();
        glBindTexture(GL_TEXTURE_2D, 0);
        glDisable(GL_BLEND);
    }
    else {
        my $self = __PACKAGE__->new(@_[1..$#_]);
        $self->draw;
    }
}

sub width {
    my ($self) = @_;
    $self->{width};
}

sub height {
    1;
}

1;

=head1 TITLE

Glop::Draw::Text - Draw text

=head1 SYNOPSIS

    Glop::Draw->Text("Hello, World!");
    
    Glop::Draw->Text(
        "Hello, World!",
        -font => 'foo.ttf',  # specify a path
        -size => 72,         # specify a rendering size (not screen size)
    );

    use Glop::Draw::Text;   # you'll have to manually use it for this form
    # create a text object in order to avoid re-rendering each time
    my $text = Glop::Draw::Text->new("Hello, World!", -size => 72);

    $text->draw;

=head1 DESCRIPTION

Draws text on the screen, with the lower-left corner at the origin.  The
height is always 1, and the width is scaled based on the width of the
text.  Use the OpenGL matrix manipulation functions to get different
behavior as usual.

=head2 Options

When using the canonical drawing syntax (C<Glop::Draw->Text>), or when creating
a new text object, this takes two options:

=over

=item -font

Sets the font.  This can be a standard font ('aircut' is the only one currently
supported) or a path to a C<ttf> font.

=item -size

Sets the I<rendering> size.  That is, higher numbers don't make what is drawn
bigger, but rather better-looking.  The default is 24.

=back

=head2 Methods

If you create a text object with:

    my $text = Glop::Draw::Text->new("Foo Bar");

Then C<$text> has the following methods:

=over

=item draw

Draw the text on the screen as described above.

=item width

Returns the width of the text in world units (not pixels).

=item height

Returns the height of the text in world units.  This is always 1.

=back

=head2 Efficiency Considerations

When you call C<Glop::Draw->Text>, the following procedure is followed:

=over

=item 1) A new pixel buffer (L<SDL::Surface>) is created.

=item 2) A new font object (L<SDL::TTFont>) is created.

=item 3) The text is drawn onto the pixel buffer using the font.

=item 4) That pixel buffer is imported onto your graphics card as a texture.

=item 5) The buffer and font objects are destroyed.

=item 6) A square with the texture applied is drawn.

=item 7) The texture is freed.

=back

When you call C<Glop::Draw::Text->new>, steps 1-5 are executed.  So, if you're
going to be drawing the text for more than one frame, it is recommended that you
create an object instead of using the "easy" form.

=head1 SEE ALSO

L<Glop>
