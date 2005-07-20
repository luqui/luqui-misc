use Test::More tests => 5;
use Data::Dumper;

BEGIN { use_ok('Class::Multimethods::Pure') }

multi foo => (Any) => sub {
    "Generic";
};

multi foo => (subtype(Any, sub { $_[0] == 6 })) => sub {
    "Six";
};

multi foo => (subtype(Any, sub { $_[0] > 10 })) => sub {
    "Big";
};

multi foo => (subtype(Any, sub { $_[0] == 40 })) => sub {
    "Forty";
};

is(foo(5),  "Generic",   "catch-all");
is(foo(6),  "Six",       "specific");
is(foo(20), "Big",       "comparison");
ok(!eval { foo(40); 1 }, "ambiguous");

# vim: ft=perl :
