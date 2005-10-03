#!/usr/bin/perl

# possibly a more memory-efficient version of L::AG.

my $indent = "";
sub t {
    my ($str) = @_;
    print STDERR "$indent$str\n";
    $indent .= "  ";
}

sub x {
    my ($ret) = @_;
    $indent = substr $indent, 2;
    $ret;
}

sub thunk(&) {
    die "More than one argument to thunk" if @_ > 1;
    my ($code) = @_;
    bless {
        thunk => $code,
    } => 'Thunk';
}

package Thunk;

sub call {
    if (my $thunk = $_[0]{thunk}) {
        delete $_[0]{thunk};
        $_[0]{value} = $thunk->();
    }
    else {
        $_[0]{value};
    }
}

package Leaf;

sub new {
    my ($class, $value) = @_;
    bless {
        value => $value,
    } => ref $class || $class;
}

sub visit {
    my ($self, $parent) = @_;
    my $compute;
    $compute = {
        min     => ::thunk { ::t "Leaf::min"; ::x $self->{value} },
        result  => ::thunk { ::t "Leaf::result"; ::x Leaf->new($compute->{gmin}->call) }, 
        gmin    => ::thunk { ::t "Leaf::gmin"; ::x $parent->{gmin}->call },
    };
    $compute;
}

package Branch;

sub new {
    my ($class, $left, $right) = @_;
    bless {
        left => $left,
        right => $right,
    } => ref $class || $class;
}

sub visit {
    my ($self, $parent) = @_;
    my ($left, $right);
    my $compute;
    $compute = {
        min => ::thunk {
            ::t "Branch::min";
            my ($lmin, $rmin) = ($left->{min}->call, $right->{min}->call);
            ::x($lmin <= $rmin ? $lmin : $rmin);
        },
        result => ::thunk { ::t "Branch::result"; ::x Branch->new($left->{result}->call, $right->{result}->call) },
        gmin => ::thunk { ::t "Branch::gmin"; ::x $parent->{gmin}->call },
    };
    ($left, $right) = ($self->{left}->visit($compute), $self->{right}->visit($compute));
    $compute;
}

package Root;

sub new {
    my ($class, $tree) = @_;
    bless {
        tree => $tree,
    } => ref $class || $class;
}

sub visit {
    my ($self, $parent) = @_;
    my $tree;
    my $compute;
    $compute = {
        result => ::thunk { ::t "Root::result"; ::x $tree->{result}->call },
        gmin   => ::thunk { ::t "Root::gmin"; ::x $tree->{min}->call },
    };
    $tree = $self->{tree}->visit($compute);
    $compute;
}

package main;

use Data::Dumper;

my $tree = Root->new(
    Branch->new(
        Leaf->new(1),
        Branch->new(
            Branch->new(
                Leaf->new(2),
                Leaf->new(3),
            ),
            Leaf->new(-3),
        ),
    ),
);

print Dumper($tree);
print Dumper($tree->visit->{result}->call);
