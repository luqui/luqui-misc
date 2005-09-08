use Test::More tests => 33;

BEGIN { use_ok('Number::Surreal') }

sub num { Number::Surreal->new(@_) }

# construct some positive numbers
my %num;
$num{0}      = num([],[]);
$num{1}      = num([$num{0}], []);
$num{2}      = num([$num{1}], []);
$num{'1/2'}  = num([$num{0}], [$num{1}]);
$num{'3/2'}  = num([$num{1}], [$num{2}]);
$num{-1}     = num([], [$num{0}]);
$num{-2}     = num([], [$num{-1}]);
$num{'-1/2'} = num([$num{-1}], [$num{0}]);
$num{'-3/2'} = num([$num{-2}], [$num{-1}]);

sub sok {
    my ($test) = @_;
    (my $newtest = $test) =~ s/(-?[\d\/]+)/\$num{'$1'}/g;
    eval("ok($newtest, '$test'); 1") or fail("$test: $@");
}

sok('0 == 0');
sok('0 != 1');
sok('1 != 2');
sok('1/2 == 1/2');
sok('1/2 != 3/2');
sok('2 != 0');
sok('0 != -1');
sok('-1 != 2');
sok('-1/2 == -1/2');
sok('1/2 != -3/2');
sok('-2 != 0');

sok('0 < 1');
sok('1 < 2');
sok('0 < 2');
sok('!(0 < 0)');
sok('0 <= 0');
sok('2 >= 3/2');
sok('-2 <= 2');

sok('0 + 0 == 0');
sok('0 + 1 == 1');
sok('1 + 1 == 2');
sok('-1 + 1 == 0');
sok('1/2 + 1/2 == 1');
sok('-3/2 + 1/2 == -1');
sok('1/2 - 1 == -1/2');

sok('0 * 0 == 0');
sok('0 * 1 == 0');
sok('-1/2 * 0 == 0');
sok('1 * 1 == 1');
sok('1 * -1 == -1');
sok('1/2 * 2 == 1');
sok('3/2 * 1/2 == num([1/2],[1])');
