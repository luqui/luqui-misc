use Test::More tests => 11;

use_ok('Class::Abstract');

ok(my $meth = Class::Abstract::Method->new('givetype', 1));
for (qw{ Object Str Num Int Ref ScalarRef Array Hash Code Glob }) {
    my $t = $_;
    $meth->add_variant($_, sub { $t });
}

is($meth->call("foo"), 'Str', 'Str');
is($meth->call(42.65), 'Num', 'Num');
is($meth->call(42),    'Int', 'Int');
is($meth->call(\my $baz), 'ScalarRef', 'ScalarRef');
is($meth->call([]),    'Array', 'Array');
is($meth->call({}),    'Hash', 'Hash');
is($meth->call(sub{}), 'Code', 'Code');
is($meth->call(\*is),  'Glob', 'Glob');

Class::Abstract::Tag->new('Foo', 'Object');
my $obj = Class::Abstract::Object::Meta->new('Foo');

is($obj->givetype, 'Object');

# vim: ft=perl :
