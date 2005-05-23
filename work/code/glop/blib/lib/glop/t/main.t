use Test::More tests => 9;
use Glop qw{:all -quiet -step 1};

is(ref(v(1,2,3)), 'ODE::Vector', "vec");

ok( within_box(v(3,4), v(2,2), v(5,5)), "within_box");
ok(!within_box(v(3,4), v(-5,-4), v(-1,-1)), "within_box");
ok(!within_box(v(3,4), v(2,2), v(5,3)), "within_box");

ok(v(3.7836, 2.991)->quantize == v(3,2), "quantize");
ok(v(-5.272, 9.3431)->quantize(2) == v(-6, 8), "quantize");
ok(v(1.9929, 5.669)->quantize(v(1,3)) == v(1,3), "quantize");
ok(v(-5,6)->quantize == v(-5,6), "quantize");

my $twice;
if (STEP != 1) {  # if everything's working, this block gets optimized away
    GONE:
    if ($twice++) {
        ok(0, "block not optimized away");
        print STDERR "STEP = " . (STEP == 1) . "\n";
        goto NEXTTEST;
    }
}

eval { goto GONE };
ok(1, "block optimized away");
NEXTTEST:

$KERNEL->norun;

# vim: ft=perl :
