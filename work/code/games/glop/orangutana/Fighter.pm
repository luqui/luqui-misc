package Fighter;

use strict;
use Glop;
use Glop::AutoGL;
use List::Util qw<min>;

use Mass;
use Wire;
use base 'Glop::Actor';

sub init {
    my ($self, $pos, $color) = @_;

    $self->{body} = Mass->make($pos, 1, 1, $color, 0, 1, "images/player_$color.png");
    $self->{theta} = 0;
    $self->{moving} = 0;
    $self->{wires} = [];
    $self->{color} = $color;
    $self->{stoppers} = 1;
    
    $self->{key_objects} = [
        Glop::Input->Mouse(motion => sub { $self->{moving}  and $self->thetastep(-$_[0]/2*STEP) },
                           '-down', left => sub { $self->{moving} and $self->fire },
                           '-up',   left => sub { $self->unfire },
                           '-down', right => sub { $self->{moving} and $self->detach },
                                    wheelup => sub { $self->{moving} and $self->lengthen },
                                    wheeldown => sub { $self->{moving} and $self->shorten },
                                    middle => sub { $self->{moving} and ::startmove() },
                        ),
    ];
}

sub position {
    my ($self) = @_;
    $self->{body}->position;
}

sub thetastep {
    my ($self, $step) = @_;
    $self->{theta} += Glop::Input->KeyState->shift ? $step / 5 : $step;
    $self->{theta} += 2 * 3.14159 while $self->{theta} < 3.14159;
    $self->{theta} -= 2 * 3.14159 while $self->{theta} >= 3.14159;
}

sub move {
    my ($self) = @_;
    $self->{moving} = 1;
}

sub nomove {
    my ($self) = @_;
    $self->{moving} = 0;
}

sub fire {
    my ($self) = @_;
    ::startmove();
    my $dir = v(cos($self->{theta}), sin($self->{theta}));
    my $newmass = Mass->make($self->{body}->position + 1.1*$dir, 0.5, 0.5, $self->{color}, 1, 0, "images/ball_$self->{color}.png");
    push @::BALLS, $newmass;
    $newmass->body->add_force($Tweak::impulse_scalar * $dir / STEP);
    $self->{body}->body->add_force(-$Tweak::impulse_scalar * $dir / STEP);       # Newton's 3rd :-)

    $self->{firing} = $newmass;

    if (@{$self->{wires}} >= $Tweak::max_limbs) {
        $self->{wires}[0]->detach;
        shift @{$self->{wires}};
    }
}

sub unfire {
    my ($self) = @_;
    return unless $self->{firing};

    push @{$self->{wires}}, Wire->make($self->{body}, 1, $self->{firing}, 0);
    undef $self->{firing};
}

sub current_wire {
    my ($self) = @_;
    my ($cur, $best) = (undef, 1e999);
    for (my $i = 0; $i < @{$self->{wires}}; $i++) {
        my $theta = $self->{wires}[$i]->theta;
        my $dist = min(abs($self->{theta} - $theta), 
                       abs($self->{theta} - (2 * 3.1415 + $theta)),
                       abs($self->{theta} - (-2* 3.1415 + $theta)));
        if ($dist < $best) {
            ($cur, $best) = ($i, $dist);
        }
    }
    return $cur;
}

sub lengthen {
    my ($self) = @_;
    return unless defined(my $wire = $self->current_wire);
    $self->{wires}[$wire]->control(-$Tweak::length_rate);
}

sub shorten {
    my ($self) = @_;
    return unless defined(my $wire = $self->current_wire);
    $self->{wires}[$wire]->control($Tweak::length_rate);
}

sub detach {
    my ($self) = @_;
    ::startmove();
    return unless defined(my $wire = $self->current_wire);
    $self->{wires}[$wire]->detach;
    splice @{$self->{wires}}, $wire, 1;
}

sub step {
    my ($self) = @_;
    return unless defined(my $wire = $self->current_wire);
    $self->{moving} && $self->{wires}[$wire]->control(0);
}

sub draw {
    my ($self) = @_;
    if ($self->{moving}) {
        preserve {
            glTranslate($self->{body}->position->list);
            glTranslate(2 * cos($self->{theta}), 2 * sin($self->{theta}), 0);
            glColor(0,0.5,1);
            Glop::Draw->Circle(-radius => 0.1);
            glTranslate(2 * cos($self->{theta}), 2 * sin($self->{theta}), 0);
            Glop::Draw->Circle(-radius => 0.2);
        };
    }
}

1;
