use Test::More tests => 4;

BEGIN { use_ok('Glop', qw{ -noinit }); }

$Glop::FSTEP = 1;   # keep away from floating point arithmetic
my $q = Glop::TransientQueue->new;

my $count = 0;
$q->enqueue( Glop::Transient->Timed($Glop::FSTEP * 10, sub { $count++ }) );
is($q->size, 1, "size");
for (0..50) {
    $q->run;
}
is($q->size, 0, "size");
is($count, 11, "Timed"); # it hits both endpoints

$KERNEL->norun;

# vim: ft=perl :
