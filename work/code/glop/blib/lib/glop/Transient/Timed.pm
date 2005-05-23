package Glop::Transient::Timed;

use strict;
use Glop -export => ['STEP'];

sub make {
    my ($pack, $time, $closure) = @_;
    
    my $total = 0;
    my $cont = 1;
    sub {
        return unless $cont;
        if ($total >= $time) {
            $total = $time;   # pretend that it's exact
            $cont = 0;
        }
        $closure->($total, $time - $total);
        $total += STEP;
    };
}

1;
