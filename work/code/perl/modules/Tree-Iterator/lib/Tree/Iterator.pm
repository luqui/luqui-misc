package Tree::Iterator;

use 5.006001;
use strict;
use warnings;

use Perl6::Attributes;
use Carp;

sub new {
    my ($class, $tree, @path) = @_;
    bless {
        root => @path ? $path[-1]{node} : $tree,
        cur  => $tree,
        path => \@path,   # list of { node => $node, key => $key }
                          # empty means we're at the root
    } => ref $class || $class;
}

sub _exists {
    my ($node, $key) = @_;
    if ("" eq $key ^ $key) {
        exists $node->{$key};
    }
    else {
        exists $node->[$key];
    }
}

sub _subscr {
    my $node = shift;
    my $key = shift;
    if (@_) {
        my $value = shift;
        if ("" eq $key ^ $key) {
            $node->{$key} = $value;
        }
        else {
            $node->[$key] = $value;
        }
    }
    else {
        if ("" eq $key ^ $key) {
            $node->{$key};
        }
        else {
            $node->[$key];
        }
    }
}

sub up {
    my ($self) = @_;
    my @path = @.path;
    my $shift = shift @path;
    @.path ? $self->new($shift->{node}, @path) : undef;
}

sub down {
    my ($self, $key) = @_;
    my @path = @.path;
    unshift @path, { node => $.cur, key => $key };

    if (_exists($.cur, $key)) {
        return $self->new(_subscr($.cur, $key), @path);
    }

    return undef;
}

sub replace {
    my ($self, $repl) = @_;
    unless (@.path) {
        croak "Cannot replace the root";
    }
    my ($parent, $key) = ($.path[0]{node}, $.path[0]{key});
    _subscr($parent, $key, $repl);
    $self->new($repl, @.path);
}
