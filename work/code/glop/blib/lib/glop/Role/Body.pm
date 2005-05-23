package Glop::Role::Body;

use strict;
use ODE;

sub compose {
    my ($class, $actor) = @_;

    $actor->{+__PACKAGE__}{body} = Glop::Physics->get->world->new_body;
    
    for my $meth (qw{position velocity rotation angular_velocity body}) {
        no strict 'refs';
        $actor->compose_method($meth, \&$meth);
    }

    if ($actor->can('geom')) {
        $actor->geom->body($actor->{+__PACKAGE__}{body});
    }
}

sub position {
    my ($self, @rest) = @_;
    $self->{+__PACKAGE__}{body}->position(@rest);
}

sub velocity {
    my ($self, @rest) = @_;
    $self->{+__PACKAGE__}{body}->velocity(@rest);
}

sub rotation {
    my ($self, @rest) = @_;
    $self->{+__PACKAGE__}{body}->rotation(@rest);
}

sub angular_velocity {
    my ($self, @rest) = @_;
    $self->{+__PACKAGE__}{body}->angular_velocity(@rest);
}

sub body {
    my ($self) = @_;
    $self->{+__PACKAGE__}{body};
}

1;
