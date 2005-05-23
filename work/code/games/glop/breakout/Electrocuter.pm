package Electrocuter;

use Glop;
use Glop::AutoGL;
use Clone;

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

my ($xs, $ys) = (4,4);

sub new {
    my ($class, $max, $min) = @_;

    bless {
        sources => [ ],
        points  => [ ],
        static  => [ ],
        array   => [ ],
        max     => 10,
        min     => -10,
    } => ref $class || $class;
}

sub max {
    my ($self, $max) = @_;
    defined $max ? $self->{max} = $max : $self->{max};
}

sub min {
    my ($self, $min) = @_;
    defined $min ? $self->{min} = $min : $self->{min};
}

sub add_source {
    my ($self, $source) = @_;
    push @{$self->{sources}}, $source;
}

sub add_static_source {
    my ($self, $source) = @_;
    for (my $x = -32; $x <= 32; $x += $xs) {
        for (my $y = 0; $y <= 48; $y += $ys) {
            $self->{array}[$x+32][$y] += $source->fsurface(v($x,$y));
        }
    }
    push @{$self->{static}}, $source;
}

sub add_point {
    my ($self, $point) = @_;
    push @{$self->{points}}, $point;
}

sub run {
    my ($self) = @_;
    for my $point (@{$self->{points}}) {
        my $pos = $point->position;
        my $field = v();
        
        for (@{$self->{sources}}, @{$self->{static}}) {
            my $f = $_->field($pos);
            $field += $f;
        }
        
        $point->apply_field($GLOBAL{electric_k} * $field);
    }
}

sub draw {
    my ($self) = @_;
    
    my @array = map { [ @$_ ] } @{$self->{array}};
    my ($max, $min) = @$self{qw{max min}};
    for (my $x = -32; $x <= 32; $x += $xs) {
        for (my $y = 0; $y <= 48; $y += $ys) {
            for (@{$self->{sources}}) {
                $array[$x+32][$y] += $_->fsurface(v($x, $y));
            }
        }
    }

    glBegin(GL_QUADS);
    for (my $x = -32; $x < 32; $x += $xs) {
        for (my $y = 0; $y < 48; $y += $ys) {
            my $c;
            $c = ($array[$x+32][$y] - $min) / ($max - $min);
            glColor($c, $c, $c);
            glVertex($x, $y);
            $c = ($array[$x+32+$xs][$y] - $min) / ($max - $min);
            glColor($c, $c, $c);
            glVertex($x+$xs, $y);
            $c = ($array[$x+32+$xs][$y+$ys] - $min) / ($max - $min);
            glColor($c, $c, $c);
            glVertex($x+$xs, $y+$ys);
            $c = ($array[$x+32][$y+$ys] - $min) / ($max - $min);
            glColor($c, $c, $c);
            glVertex($x, $y+$ys);
        }
    }
    glEnd();
}

1;
