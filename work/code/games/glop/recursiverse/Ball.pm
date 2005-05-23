package Ball;

use Glop;
use Glop::AutoGL;
use Perl6::Attributes;

sub new {
    my ($class) = @_;
    bless { 
        momentum => 150,
        mass     => 2,
        ypos     => 0,
        yvel     => 0,
    } => ref $class || $class;
}

sub mass {
    my ($self) = @_;
    $.mass;
}

sub velocity {
    my ($self) = @_;
    $.momentum / $.mass;
}

sub yvel {
    my ($self) = @_;
    $.yvel;
}

sub accel {
    my ($self, $dir) = @_;
    $.yvel += STEP * $dir;
}

sub size {
    my ($self) = @_;
    1.3 * sqrt($.mass);
}

sub ypos { 
    my ($self) = @_;
    $.ypos;
}

sub move {
    my ($self, $dir) = @_;
    $.ypos += STEP * $dir;
}

sub grow {
    my ($self, $dir) = @_;
    $.mass += STEP * $dir;
    $.mass < 1   and $.mass = 1;
    $.mass > 5   and $.mass = 5;
}

sub momentum { 
    my ($self) = @_;
    $.momentum;
}

sub add_momentum {
    my ($self, $dir) = @_;
    $.momentum += STEP * $dir;
}

sub step {
    my ($self) = @_;
    $.ypos += STEP * $.yvel;
}

1;
