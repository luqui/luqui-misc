package Glop::Texture;

use Glop ();
use Carp;

sub new {
    my ($class, $image) = @_;
    croak "Usage: Glop::Texture->new('foo.bmp')\n" unless $image;
    my $surface = SDL::Surface->new(-name => $image) 
            or croak "Couldn't load '$image'";
    $surface->rgba();

    my $width = $surface->width;
    my $height = $surface->height;

    croak "Image '$image' width and height must be powers of two"
        if (log($width)/log(2)) =~ /\./ || (log($height)/log(2)) =~ /\./;

    package Glop::GLSpace;
    glEnable(GL_TEXTURE_2D);
    my ($tex) = @{glGenTextures(1)};
    glBindTexture(GL_TEXTURE_2D, $tex);
    glTexParameter(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameter(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexImage2D(GL_TEXTURE_2D, 0, 4,
                 $width, $height,
                 0, GL_RGBA, GL_UNSIGNED_BYTE,
                 $surface->pixels);
    glBindTexture(GL_TEXTURE_2D, 0);

    bless {
        tex => $tex,
    } => ref $class || $class;
}

sub bind {
    my ($self) = @_;
    package Glop::GLSpace;
    glBindTexture(GL_TEXTURE_2D, $self->{tex});
}

sub unbind {
    my ($self) = @_;
    package Glop::GLSpace;
    glBindTexture(GL_TEXTURE_2D, 0);
}

sub id {
    my ($self) = @_;
    $self->{tex};
}

sub DESTROY {
    my ($self) = @_;
    Glop::GLSpace::glDeleteTextures($self->{tex});
}

1;
