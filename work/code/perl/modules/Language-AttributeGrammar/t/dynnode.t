#!/usr/bin/perl

# from the PerlMonks node http://perlmonks.org/?node_id=534671

use strict;
use warnings;

use Test::More tests => 2;
BEGIN { use_ok('Language::AttributeGrammar') }

package Leaf;

sub new{
  return bless { value => $_[1] }, 'Leaf';
}

package Branch;

sub new{
  return bless { value => $_[1], _list => undef }, 'Branch';
}

sub add_child{
  my $self = shift;
  push @{ $self->{_list} }, @_;
  return $self;
}

sub list {
  if (@_) {
    bless { head => $_[0], tail => list(@_[1..$#_]) }, 'Cons';
  }
  else {
    bless {}, 'Nil';
  }
}

sub children{
  list( @{ $_[0]->{_list} });
}

package main;

my $grammar = new Language::AttributeGrammar <<'EOG';

Branch: $/.len          = { 1 + $<children>.len }
Leaf:   $/.len          = { 1 }
Cons: $/.len            = { $<head>.len + $<tail>.len }
Nil:  $/.len            = { 0 }

EOG

my $tree = Branch->new(3)->add_child(
     Branch->new(1.1)->add_child(
          Leaf->new(1),
          Leaf->new(1.2)
    ),
     Branch->new(2.0)->add_child(
          Leaf->new(2.1),
          Leaf->new(2.2),
    )
 );

my $result = $grammar->apply($tree, 'len');
is($result, 7, "correct number of nodes counted");

# vim: ft=perl :
