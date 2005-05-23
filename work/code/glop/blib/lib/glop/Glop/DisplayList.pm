package Glop::DisplayList;

use strict;
use Glop ();

sub new {
    my ($class) = @_;

    package Glop::GLSpace;
    my $list = glGenLists(1) 
             or die "Couldn't create display list: " . glErrorString(glGetError());
    bless {
        id => $list,
    } => ref $class || $class;
}

sub draw {
    my ($self) = @_;
    
    package Glop::GLSpace;
    glCallList($self->{id});

    $self;
}

sub record {
    my ($self, $exec) = @_;

    package Glop::GLSpace;
    glNewList($self->{id}, $exec ? GL_COMPILE : GL_COMPILE_AND_EXECUTE);

    $self;
}

sub done {
    my ($self) = @_;
    package Glop::GLSpace;
    glEndList();
    
    $self;
}

sub DESTROY {
    my ($self) = @_;
    
    package Glop::GLSpace;
    glDeleteLists($self->{id}, 1);
}

1;
