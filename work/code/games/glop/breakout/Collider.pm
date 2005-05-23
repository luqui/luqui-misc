package Collider;

use Glop;
use Class::Multimethods;

multimethod 'collide';

resolve_ambiguous collide => sub { { } };

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

sub new {
    my ($class) = @_;

    bless {
        objects => { },   # map from geoms to objects
    } => ref $class || $class;
}

sub register {
    my ($self, $geom, $object) = @_;
    $self->{objects}{$geom} = $object;
}

sub collider {
    my ($self, $a, $b) = @_;

    if ($a->is_space || $b->is_space) {
        $a->multi_collide($b, sub { $self->collider(@_) });
    }
    elsif (my @points = $a->collide($b)) {
        my ($ao, $bo) = @{$self->{objects}}{$a, $b};
        my $result = { };
            
        if ($ao && $bo) {
            $result = collide($ao, $bo);
        }

        if ($result) {
            $result->{mode}   ||= [ qw{ Bounce } ];
            $result->{bounce} ||= 1;
            $result->{mu}     ||= 1e999;
            for my $point (@points) {
                my $param = { %$result };
                $param->{pos}    ||= $point->pos;
                $param->{normal} ||= $point->normal;
                $param->{depth}  ||= $point->depth;
                
                my $j = ODE::Joint::Contact->new(
                    $GLOBAL{ode_world},
                    $GLOBAL{contact_group},
                    $param,
                );
                $j->attach($a->body, $b->body);
            }
        }
    }
}

1;
