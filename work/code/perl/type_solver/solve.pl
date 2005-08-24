#!/usr/bin/perl

use strict;
use warnings;
no warnings 'uninitialized';

use Graph::Directed;
use Graph::TransitiveClosure;

# sub bar(::C $x --> ::C) { $x }
# sub foo(::A $x --> ::B) { bar($x) }
# my Int $a = foo("baz");

my $g = Graph::Directed->new;
for my $edge (
    [qw<Str A>],
    [qw<A   C>],
    [qw<C   B>],
    [qw<B   Int>],    
) {
    $g->add_vertex($edge->[0]);
    $g->add_vertex($edge->[1]);
    $g->add_edge($edge->[0], $edge->[1]);
}

my $tg = Graph::TransitiveClosure->new($g);
print "$tg\n";

for my $va ($tg->vertices) {
    for my $vb ($tg->vertices) {
        next if $va eq $vb;
        if ($tg->has_edge($va, $vb) && $tg->has_edge($vb, $va)) {
            print "$va == $vb\n";
        }
    }

}
