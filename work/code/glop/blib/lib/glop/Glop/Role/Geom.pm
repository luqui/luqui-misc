package Glop::Role::Geom;

use strict;
use ODE;
use Carp;

sub compose {
    my ($class, $actor, $geom) = @_;

    if (ref $geom eq 'ARRAY') {
        $actor->{+__PACKAGE__}{geom} = 
        $geom = 
            "ODE::Geom::$geom->[0]"->new(
                Glop::Physics->get->space,
                @$geom[1..$#$geom]);
    }
    elsif (ref $geom) {
        $actor->{+__PACKAGE__}{geom} = $geom;
    }
    else {
        croak "compose: Usage: Glop::Role->Geom(\$actor, [ ... ])";
    }
    
    for my $meth (qw{geom}) {
        $actor->compose_method($meth, \&$meth);
    }

    if ($actor->can('body')) {
        $geom->body($actor->body);
    }
    
    Glop::Physics->get->register($geom, $actor);
}

sub geom {
    my ($self) = @_;
    $self->{+__PACKAGE__}{geom};
}

1;
