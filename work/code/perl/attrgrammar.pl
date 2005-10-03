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
        min     => sub { ::t "Leaf::min"; ::x $self->{value} },
        result  => sub { ::t "Leaf::result"; ::x Leaf->new($compute->{gmin}->()) }, 
        gmin    => sub { ::t "Leaf::gmin"; ::x $parent->{gmin}->() },
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
        min => sub {
            ::t "Branch::min";
            my ($lmin, $rmin) = ($left->{min}->(), $right->{min}->());
            ::x($lmin <= $rmin ? $lmin : $rmin);
        },
        result => sub { ::t "Branch::result"; ::x Branch->new($left->{result}->(), $right->{result}->()) },
        gmin => sub { ::t "Branch::gmin"; ::x $parent->{gmin}->() },
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
        result => sub { ::t "Root::result"; ::x $tree->{result}->() },
        gmin   => sub { ::t "Root::gmin"; ::x $tree->{min}->() },
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
print Dumper($tree->visit->{result}->());
