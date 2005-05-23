use Test::More tests => 27;

BEGIN { use_ok('Glop::TransientQueue'); }

ok(my $q = Glop::TransientQueue->new, "new");

my $var = 0;
sub mkiter {
    my $iter = shift;
    sub {
        return unless $iter;
        --$iter; ++$var;
    };
}

$q->push(mkiter(2));

$q->run;  # $iter == 1
is($var, 1, "run");
is($q->size, 1, "size");
$q->run;  # $iter == 0
is($var, 2, "run");
is($q->size, 1, "size");
$q->run;  # $iter == 0 and dequeued
is($var, 2, "run");
is($q->size, 0, "dequeue");
eval { $q->run };
ok(!$@, "run when empty");

$q->push(mkiter(1), mkiter(0), mkiter(1));
is($q->size, 3, "size");
$q->run;
is($var, 3, "run");
is($q->size, 3, "size");
$q->run;
is($var, 4, "run");
is($q->size, 1, "dequeue");
$q->run;
is($var, 4, "run");
is($q->size, 0, "dequeue");

$q->push(mkiter(2));
my ($orig, $new) = $q->fork;
ok($orig && $new, "fork");
is($orig->size, 1, "fork");
is($new->size, 0, "fork");
is($q->size, 1, "parallel size");
$new->push(mkiter(0), mkiter(1));
is($q->size, 2, "parallel size");
$q->run;
is($var, 6, "parallel run");
is($q->size, 1, "parallel size");
$q->run;
is($var, 7, "parallel run");
is($q->size, 1, "parallel size");
$q->run;
is($var, 7, "parallel dequeue");
is($q->size, 0, "parallel size");

# vim: ft=perl :
