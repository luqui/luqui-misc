#!/usr/bin/perl

package Foo;

sub foo { }

package Bar;

use base 'Foo';

package Baz;

package main;

use Benchmark qw{cmpthese};

my $foo = bless { } => Foo;
my $bar = bless { } => Bar;
my $baz = bless { foo => sub { } } => Baz;
my $abz = bless [ sub { } ] => Baz;

cmpthese 1_000_000, {
    method  => sub { $foo->foo },
    derived => sub { $bar->foo },
    hashed  => sub { $baz->{foo}->() },
    arrayed => sub { $abz->[0]->() },
};
