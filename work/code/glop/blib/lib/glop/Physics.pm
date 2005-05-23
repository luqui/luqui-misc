package Glop::Physics;

use strict;
use Glop ();
use ODE;

use base 'Glop::Floater';

sub init {
    my ($self) = @_;

    $self->{world}    = ODE::World->new;
    $self->{queue}    = [ ];
    $self->{objects}  = { };
    $self->{group}    = ODE::JointGroup->new;
    $self->{space}    = ODE::Geom::Space::Hash->new;
    $self->{callback} = sub { 1 };
    $self->{enabled}  = 1;
}

sub enable {
    my ($class) = @_;

    $Glop::KERNEL->heap->{"*$class"} ||= $class->make;
}

BEGIN { *get = \&enable; }

sub clear {
    my ($self) = @_;
    $self->init;
}

sub suspend {
    my ($self) = @_;
    $self->{enabled} = 0;
}

sub resume {
    my ($self) = @_;
    $self->{enabled} = 1;
}

sub world {
    my ($self) = @_;
    $self->{world};
}

sub space {
    my ($self) = @_;
    $self->{space};
}

sub register {
    my ($self, $geom, $object) = @_;
    $self->{objects}{$geom} = $object;
}

sub callback {  # XXX: temporary until we have some builtin mmd
    my ($self, $callback) = @_;
    $self->{callback} = $callback;
}

sub collider {
    my ($self, $a, $b) = @_;

    if ($a->is_space || $b->is_space) {
        $a->multi_collide($b, sub { $self->collider(@_) });
    }
    elsif (my @points = $a->collide($b)) {
        # We can't callback from here, because we can't be
        # sure that we're not going to modify a geom from
        # within the callback.
        push @{$self->{queue}}, {
            geom_a => $a,
            geom_b => $b,
            obj_a  => $self->{objects}{$a},
            obj_b  => $self->{objects}{$b},
            points => \@points,
        };
    }
}

sub step {
    my ($self) = @_;

    return unless $self->{enabled};

    $self->{group}->empty;

    $self->{space}->space_collide(sub { $self->collider(@_) });

    while (my $col = shift @{$self->{queue}}) {
        my $ret = $self->{callback}->($col);
        if ($ret) {
            unless (ref $ret) {
                $ret = {
                    mode => [ 'Bounce' ],
                    bounce => 0.2,
                    mu => 1,
                };
            }

            for my $point (@{$col->{points}}) {
                my $j = ODE::Joint::Contact->new(
                    $self->{world},
                    $self->{group},
                    {
                        pos => $point->pos,
                        normal => $point->normal,
                        depth => $point->depth,
                        %$ret,
                    },
                );
                $j->attach($col->{geom_a}->body, $col->{geom_b}->body);
            }
        }
    }

    $self->{world}->quickstep(Glop::STEP());
}

1;
