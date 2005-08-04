use Test::More tests => 12;

BEGIN { use_ok('Symbol::Opaque') }

defsym('foo'); 
defsym('bar'); 

{
    ok(foo(my $x) << foo(10), "binding succeeded");
    is($x, 10, "simple");
}

{
    ok(!( foo(my $x) << 42 ), "binding failed");
}

{
    ok(foo(my $x, bar(my $y)) << foo(1, bar(2)), "binding succeeded");
    is($x, 1, "x binding");
    is($y, 2, "y binding");
} 

{
    ok(foo(1, bar(2)) << foo(1, bar(2)), "trivial constant binding");
}

{
    ok(!( foo(my $x, 2) << foo(2, 3) ), "binding failed");
    ok(!defined $x, "x not bound even after partial success");
}

{
    my $x = "hello";
    ok(!( foo($x) << foo(42) ), "binding fails on already-defined variables");
    is($x, "hello", "x is preserved");
}

# vim: ft=perl :
