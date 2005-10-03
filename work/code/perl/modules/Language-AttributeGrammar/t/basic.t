use strict;
use warnings;

use Test::More tests => 14;
use Test::Exception;

my $m; BEGIN { use_ok($m = 'Language::AttributeGrammar') }

can_ok($m, "new");
can_ok($m, "apply");

sub mkg { $m->new(shift) }
sub mko { my $c = shift; bless { @_ }, $c }
sub apply { mkg(shift)->apply(@_) }

{
	my $r = apply('Foo: gorch($$) = { 42 }', mko("Foo"));

	lives_ok { $r->gorch } "ok to access valid attribute";
	is($r->gorch, 42, "the attribute's value");

	dies_ok { $r->quxx } "fatal to access invalid attribute";
}

{
	my $r = apply(<<'EOG', mko("Foo"));
Foo: gorch($$) = { 42 }
Foo: bar($$) = { gorch($$) / 2 }
EOG

	is($r->bar, 21, "dependant attributes on the same node");
}

{
	my $r = apply(<<'EOG', mko("Foo", bar => mko("Bar")));
Foo: value($$) = { 3 * value($.bar) }
Bar: value($$) = { 4 }
EOG

	is($r->value, 12, "one level of synthesized attributes");
}


{
	my $r = apply(<<'EOG', mko(Foo => child => mko(Foo => child => mko(Foo => child => mko("Bar")))));
Foo: value($$) = { 3 * value($.child) }
Bar: value($$) = { 4 }
EOG

	is($r->value, 3 * 3 * 3 * 4, "N levels of synthesized attributes");
}

{
	my $r = apply(<<'EOG', mko("Foo", bar => mko("Bar")));
Foo: parent_value($.bar) = { 3 }
Foo: value($$) = { value($.bar) }
Bar: value($$) = { 4 * parent_value($$) }
EOG

	is($r->value, 12, "one level of inherited attributes");
}

{
	my $r = apply(<<'EOG', mko(Root => child => mko(Foo => child => mko(Foo => child => mko(Foo => child => mko("Bar"))))));
Root: parent_value($.child) = { 1 }
Root: value($$) = { value($.child) }

Foo: parent_value($.child) = { 3 * parent_value($$) }
Foo: value($$) = { value($.child) }

Bar: value($$) = { 4 * parent_value($$) }
EOG

	is($r->value, 3 * 3 * 3 * 4, "N levels of inherited attributes");
}

{
	is(apply('ROOT: value($$) = { 5 }', mko("Foo"))->value, 5, "ROOT pseudonnode");
}

{
	my $r = apply(<<'EOG', mko(Foo => child => mko("Bar")));
ROOT: foo($$) = { 5 }
Foo: bar($.child) = { foo($$) }
Foo: bah($$) = { bah($.child) }
Bar: bah($$) = { bar($$) + 10 }
EOG
	is($r->bah, 15, "ROOT inherits");
}

{
	my $r = apply(<<'EOG', mko(Foo => child => mko("Bar")));
ROOT: foo($$) = { 5 }
Foo: foo($$) = { bar($.child) }
Bar: bar($$) = { 10 }
EOG
	is($r->foo, 5, "definition under ROOT overrides definition over class");
}
