#!/usr/bin/perl

my @sym = (
    [ M => 1000 ],
    [ D => 500  ],
    [ C => 100  ],
    [ L => 50   ],
    [ X => 10   ],
    [ V => 5    ],
    [ I => 1    ],
);

sub convert {
    my ($num) = @_;
    my $i = 0;
    my $out;
   
    SYM:
    while ($num > 0 && $i < @sym) {
        my ($sym, $value) = @{$sym[$i]};

        if ($num >= $value) {
            $out .= $sym;
            $num -= $value;
        }
        else {
            for (reverse @sym[$i..$#sym]) {
                if ($num >= $value - $_->[1] && $value - $_->[1] > $_->[1]) {
                    $out .= $_->[0] . $sym;
                    $num -= $value - $_->[1];
                    next SYM;
                }
            }
            $i++;
        }
    }
    $out;
}

while (<>) {
    chomp;
    print convert($_), "\n";
}

