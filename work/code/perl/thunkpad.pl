#!/usr/bin/perl

package Thunk;

sub new {
    my ($class, $code) = @_;
    bless {
        thunk => $code,
    } => ref $class || $class;
}

sub call {
    if (my $thunk = $_[0]{thunk}) {
        delete $_[0]{thunk};
        $_[0]{value} = $thunk->();
    }
    else {
        $_[0]{value};
    }
}

package Destroyer;

sub new {
    my ($class) = @_;
    my $self = bless {} => ref $class || $class;
    print STDERR "Create $self\n";
    $self;
}

sub DESTROY {
    print STDERR "Destroy $_[0]\n";
}

package main;

sub thunk(&) {
    my ($code) = @_;
    Thunk->new($code);
}

sub example {
    print STDERR "Create variables\n";
    my ($x, $y, $z) = (Destroyer->new, Destroyer->new, Destroyer->new);
    print STDERR "Create thunks\n";
    my ($tha, $thb) = (
        thunk { $x; 0 },
        thunk { $y; 0 },
    );
    print STDERR "Evaluate thunk with x\n";
    $tha->call;
    print STDERR "Returning\n";
    ($tha, $thb);
}

{
    my ($tha, $thb) = example();
    print STDERR "Returned\n";
}

print STDERR "Exited\n";
