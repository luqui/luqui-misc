#!/usr/bin/perl

use Language::AttributeGrammar;

my $grammar = new Language::AttributeGrammar <<'EOG';

ROOT: $/.a    = { print "Root:a $/\n"; $/.d + 1 }
    | $/.c    = { print "Root:c $/\n"; $/.b + 1 }

Foo: $<bar>.a = { print "Foo:a $/\n"; $/.a + 1 }
   | $/.b     = { print "Foo:b $/\n"; $<bar>.b + 1 }
   | $<bar>.c = { print "Foo:c $/\n"; $/.c + 1 }
   | $/.d     = { print "Foo:d $/\n"; $<bar>.d + 1 }

Nil: $/.b     = { print "Nil:b $/\n"; $/.a + 1 }
   | $/.d     = { print "Nil:d $/\n"; $/.c + 1 }

EOG

my $tree = bless { bar => (bless { bar => (bless { } => 'Nil') } => 'Foo') } => 'Foo';

print $grammar->apply($tree, 'd'), "\n";
