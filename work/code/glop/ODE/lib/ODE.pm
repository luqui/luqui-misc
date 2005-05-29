package ODE;

use 5.006001;
no warnings;

our $VERSION = 0.01;

use XSLoader;
XSLoader::load('ODE', $VERSION);

END {
    _close_ode();
}

package ODE::World;

sub new {
    my ($class) = @_;
    _make();
}

sub DESTROY {
    my ($self) = @_;
    $self->_destroy;
}

sub joint {
    my ($self, $type, @rest) = @_;
    "ODE::Joint::$type"->new($self, @rest);
}

package ODE::Body;

package ODE::JointGroup;

sub new {
    my ($class) = @_;
    _make();
}

sub DESTROY {
    my ($self) = @_;
    $self->_destroy;
}

package ODE::Joint;

use Carp;

sub new {
    my ($class, $world, $group) = @_;
    &{"$class\::_make"}($world, $group);
}

sub DESTROY {
    my ($self) = @_;
    $self->_destroy;
}

sub set_params {
    my ($self, @params) = @_;

    while (@params) {
        my ($k, $v) = splice @params, 0, 2;
        my ($error, $const) = ODE::constant("dParam$k");
        croak $error if $error;
        $self->_param($const, $v);
    }
}

sub get_param {
    my ($self, $param) = @_;
    my ($error, $const) = ODE::constant("dParam$param");
    croak $error if $error;
    $self->_param($const);
}

BEGIN {
    for (qw{Ball Hinge Slider Contact Universal 
            DoubleHinge Fixed AngularMotor Plane2D}) {
        *{"ODE::Joint::$_\::ISA"} = [ ODE::Joint ];
    }
}

package ODE::Joint::Contact;

use List::Util qw{reduce};
use Carp;

sub array_to_flags {
    my $ret = reduce { $a | $b } 
    map { 
         my ($error, $const) = ODE::constant("dContact$_");
         croak $error if $error;
         $const;
    } 
    @_;
}

sub new {
    my ($class, $world, $group, $data) = @_;
    $data ||= {};
    if (exists $data->{mode} && ref($data->{mode}) eq 'ARRAY') {
        $data->{mode} = array_to_flags @{$data->{mode}};
    }
    _make($world, $group, $data);
}

package ODE::Geom;

sub new {
    my ($class, $parent, @more) = @_;
    my $ret = &{"$class\::_make"}($parent, @more);
    $ret;
}

sub DESTROY {
    my ($self) = @_;
    $self->_destroy;
}

BEGIN {
    for (qw{Space Sphere Box Plane CappedCylinder 
            Cylinder Ray Transform}) {
        *{"ODE::Geom::$_\::ISA"} = [ ODE::Geom ];
    }
}

package ODE::Geom::Space;

BEGIN {
    for (qw{Simple Hash QuadTree}) {
        *{"ODE::Geom::Space::$_\::ISA"} = [ ODE::Geom::Space ];
    }
}

package ODE::Geom::Plane;

sub new {
    my ($class, $parent, $c, $dir) = @_;
    $dir /= $dir->norm;
    my $param = $c * $dir;
    _make($parent, $dir, $param);
}

sub center_direction {
    my ($self, $c, $dir) = @_;
    my $param;
    if (defined $c && defined $dir) {
        $dir /= $dir->norm;
        $param = $c * $dir;
        $self->normal_param($dir, $param);
    } 
    else {
        ($dir, $param) = $self->normal_param;
        $c = $dir * $param;
    }
    ($c, $dir);
}

package ODE::Vector;

# This class posesses value semantics and a super-secret internal
# data structure.  To derive from it, delegate to it.

use overload
    '='  => \&clone,
    '+' => \&sum,
    '-' => sub { $_[2] ? $_[1] + -$_[0] : $_[0] + -$_[1] },
    '*'  => sub {
        ref $_[1] eq 'ODE::Vector' ? 
            dot(@_[0,1]) : 
            scale(@_[0,1])
    },
    '/' => sub {
        die "Can't divide by a vector" if $_[2] || ref $_[1] eq 'ODE::Vector';
        $_[0] * (1 / $_[1]);
    },
    'x' => \&cross,
    neg => sub { $_[0]->neg },
    '""' => sub {
        my $self = shift;
        '<' . $self->x . ',' . $self->y . ',' . $self->z . '>'
    },
    "==" => \&equals,
    "!=" => sub { !($_[0] == $_[1]) },
    bool => sub { $_[0]->norm > 0.0005 },
    '@{}'=> sub { [ $_[0]->list ] },
;

sub new {
    no warnings 'uninitialized';
    my ($class, $x, $y, $z) = @_;
    _make($x, $y, $z);
}

package ODE::Quaternion;

use Carp;

# See the comments for ODE::Vector

use overload
    '=' => \&clone,
    '*' => \&prod,
    '@{}' => sub { [ $_[0]->list ] },
    '""' => sub { 
        my $self = shift;
        my @comp = $self->list;
        "($comp[0] <$comp[1],$comp[2],$comp[3]>)"
    };

sub new {
    my ($class, @args) = @_;
    if (@args == 0) {
        _make_identity();
    }
    elsif (@args == 2 && ref $args[1] eq 'ODE::Vector') {
        _make_angle_axis($args[0], $args[1]);
    }
    elsif (@args == 2 && ref $args[1] eq 'ARRAY') {
        _make_angle_axis($args[0], ODE::Vector->new(@{$args[1]}));
    }
    elsif (@args == 4) {
        _make_direct(@args);
    }
    else {
        croak "ODE::Quaternion::new: parameters not understood";
    }
}

package ODE::Mass;

sub new {
    my ($class, $mass) = @_;
    my $self = _make();
    $self->mass($mass);
    $self;
}

1;

__END__

=head1 TITLE

ODE - Interface to the Open Dynamics Engine
