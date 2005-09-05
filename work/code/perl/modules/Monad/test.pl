use Test::More tests => 13;

BEGIN { 
    use_ok('Monad');
    use_ok('Monad::Id');
    use_ok('Monad::Coro');
}

sub mul2 {
    my $id = shift;
    DO {
        my $orig <- $id;
        Monad::Id->RETURN(2 * $orig);
    }
}

is(mul2(Monad::Id->RETURN(8))->get, 16, "single-value identity");

sub mreverse {
    my $id = shift;
    DO {
        my @values <- $id;
        Monad::Id->RETURN(reverse @values);
    }
}

is_deeply([mreverse(Monad::Id->RETURN(1,2,3))->get], [3,2,1], "multi-value identity");

sub sums {
    DO {
        my $a <- [0,1];
        my $b <- [2,4];
        [ $a+$b ];
    }
}

is_deeply(sums(), [2,4,3,5], "list monad");

sub multis {
    DO {
        my $a <- [0,1];
        if ($a) DO {
            my $b <- [2,4];
            [ $a + $b ];
        }
        else DO {
            my $b <- [8,16];
            [ $a + $b ];
        }
    }
}

is_deeply(multis(), [8,16,3,5], "nested do blocks");

sub next3 {
    my ($first) = @_;
    DO {
        ^yield $first+1;
        ^yield $first+2;
        ^yield $first+3;
    }
}

my $coro = Monad::Coro->new(\&next3);
is($coro->start(1), 2, "coro");
ok(!$coro->done,       "coro not done");
is($coro->next,     3, "coro");
is($coro->next,     4, "coro");
ok(!defined $coro->next, "coro stops");
ok($coro->done,       "done");

# vim: ft=perl :
