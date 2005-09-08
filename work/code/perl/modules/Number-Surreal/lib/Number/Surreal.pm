package Number::Surreal;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

use Carp;

# util functions for the operators
my $sadd = sub { 
    my ($xx, $yy) = @_;  
    defined($xx) && defined($yy) ? ($xx + $yy) : (); 
};
my $smul = sub {
    my ($xx, $yy) = @_;
    defined($xx) && defined($yy) ? ($xx*$yy) : (),
};
my $sneg = sub {
    my ($xx) = @_;
    defined($xx) ? (-$xx) : ();
};

use overload
    '<=' => sub {
        my ($x, $y) = @_;
        my ($xL, $yR) = ($x->L, $y->R);
        not (defined($xL) && $y <= $xL or defined($yR) && $yR <= $x);
    },
    '>=' => sub {
        my ($x, $y) = @_;
        $y <= $x;
    },
    '<'  => sub {
        my ($x, $y) = @_;
        not $y <= $x;
    },
    '>'  => sub {
        my ($x, $y) = @_;
        not $x <= $y;
    },
    '==' => sub {
        my ($x, $y) = @_;
        $x <= $y && $y <= $x;
    },
    '!=' => sub {
        my ($x, $y) = @_;
        not $x == $y;
    },
    '+' => sub {
        my ($x, $y) = @_;
        my ($xL, $yL, $xR, $yR) = ($x->L, $y->L, $x->R, $y->R);
        Number::Surreal->new([
            $sadd->($xL, $y), $sadd->($x, $yL)
        ], [
            $sadd->($xR, $y), $sadd->($x, $yR)
        ]);
    },
    'neg' => sub {
        my ($x) = @_;
        Number::Surreal->new([
            defined($x->R) ? (-$x->R) : (),
        ], [
            defined($x->L) ? (-$x->L) : (),
        ]);
    },
    '-' => sub {
        my ($x, $y) = @_;
        $x + (-$y);
    },
    '*' => sub {
        my ($x, $y) = @_;
        my ($xL, $yL, $xR, $yR) = ($x->L, $y->L, $x->R, $y->R);
        Number::Surreal->new([
            $sadd->($sadd->($smul->($xL, $y), $smul->($x, $yL)), $sneg->($smul->($xL, $yL))),
            $sadd->($sadd->($smul->($xR, $y), $smul->($x, $yR)), $sneg->($smul->($xR, $yR))),
        ], [
            $sadd->($sadd->($smul->($xL, $y), $smul->($x, $yR)), $sneg->($smul->($xL, $yR))),
            $sadd->($sadd->($smul->($xR, $y), $smul->($x, $yL)), $sneg->($smul->($xR, $yL))),
        ]); 
    },
    '""' => sub {
        overload::StrVal($_[0]),
    },
;

# god damnit, List::Util's min and max are too smart
sub min {
    confess "min called with 0 arguments" unless @_;
    my $min = $_[0];
    for (@_[1..$#_]) {
        if ($_ < $min) { $min = $_ }
    }
    return $min;
}

sub max {
    confess "max called with 0 arguments" unless @_;
    my $max = $_[0];
    for (@_[1..$#_]) {
        if ($_ > $max) { $max = $_ }
    }
    return $max;
}

sub new {
    my ($class, $L, $R) = @_;
    croak "Usage: Number::Surreal->new([num1, num2, ...], [num3, num4, ...])"
        unless ref $L eq 'ARRAY' && ref $R eq 'ARRAY';
    bless {
        L => @$L ? max(@$L) : undef,
        R => @$R ? min(@$R) : undef,
    } => ref $class || $class;
}

sub L {   # returns the greatest left element // undef
    my ($self) = @_;
    $self->{L};
}

sub R {   # the least right element // undef
    my ($self) = @_;
    $self->{R};
}

1;
