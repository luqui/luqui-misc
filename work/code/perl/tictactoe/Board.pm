package Board;

use strict;

sub new {
    bless [ map { [ (0) x 3 ] } 1..3 ] => ref $_[0] || $_[0];
}

sub clone {
    my ($self) = @_;
    bless [ map { [ @$_ ] } @$self ] => ref $self;
}

sub open {
    my ($self, $x, $y) = @_;
    !$self->[$x-1][$y-1];
}

sub move {
    my ($self, $xo, $x, $y) = @_;
    $self->[$x-1][$y-1] = $xo;
}

sub winner {
    my ($self) = @_;
    my @s = @$self;   # faster access
    for my $x (0..2) {
        if ($s[$x][0] && $s[$x][0] eq $s[$x][1] && $s[$x][1] eq $s[$x][2]) {
            return $s[$x][0];
        }
        if ($s[0][$x] && $s[0][$x] eq $s[1][$x] && $s[1][$x] eq $s[2][$x]) {
            return $s[0][$x];
        }
    }
    if ($s[0][0] && $s[0][0] eq $s[1][1] && $s[1][1] eq $s[2][2]) {
        return $s[0][0];
    }
    if ($s[0][2] && $s[0][2] eq $s[1][1] && $s[1][1] eq $s[2][0]) {
        return $s[0][2];
    }
    return;
}

sub display {
    my ($self) = @_;
    my @b = map { [ map { $_ ? $_ : ' ' } @$_ ] } @$self;
    print <<EOB;
    1   2   3
  +---+---+---+
a | $b[0][0] | $b[0][1] | $b[0][2] |
  +---+---+---+
b | $b[1][0] | $b[1][1] | $b[1][2] |
  +---+---+---+
c | $b[2][0] | $b[2][1] | $b[2][2] |
  +---+---+---+
EOB
}

1;
