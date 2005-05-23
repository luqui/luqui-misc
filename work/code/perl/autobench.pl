#!/usr/bin/perl

package Foo;

sub new {
    bless {} => ref $_[0] || $_[0];
}

sub go { }

package Bar;

sub new {
    bless {} => ref $_[0] || $_[0];
}

sub AUTOLOAD { }

sub gu { }

package main;

use Benchmark qw{cmpthese};

my $foo = new Foo;
my $bar = new Bar;

cmpthese(1_000_000, {
    Plain => sub { $foo->go },
    Auto  => sub { $bar->go },
});
