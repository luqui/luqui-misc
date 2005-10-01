use strict;
use warnings;

use Test::More tests => 6;
use Test::Exception;

my $m; BEGIN { use_ok($m = 'Language::AttributeGrammar') }

sub mkg { $m->new(shift) }
sub mko { my $c = shift; bless { @_ }, $c }
sub apply { mkg(shift)->apply(@_) }


throws_ok {
	mkg('syntax error b{{{ {lkjahdtkjhat #%$!%^!#*^#!^!'); # i really hope that's not perl ;-)
} qr/Parse error/, "bad grammer makes a syntax error"; # FIXME - P::RD emits a warning that we cannot mute (C?)

throws_ok {
	apply('Foo: gorch($$) = { $.doesnt_exist }', mko("Foo"))->gorch;
} qr/access.*doesnt_exist/i, "can't access in-existent field in node";

dies_ok {
	apply('Foo: gorch($$) = { doesnt_exist($$) }', mko("Foo"))->gorch;
} "can't call undefined function/attr";


throws_ok {
	apply('Cons: depth($.tail) = { 1 + depth($$) }', mko(Cons => tail => mko(Cons => tail => mko("Nil"))))->depth;
} qr/cannot find.*attribute.*depth/i, "in-existent attribute (lack of root)";

throws_ok {
	apply(<<'EOG', mko(Cons => tail => mko(Cons => tail => mko("Nil"))))->length;
Cons: depth($.tail) = { 1 + depth($$) }
Cons: length($$) = { length($.tail) }
Nil: length($$) = { depth($$) }
EOG
} qr/nonlinear attribute/i, "nonlinear attribute";


