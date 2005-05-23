package Paddle;

use strict;

use Glop;
use Glop::AutoGL;

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

use base 'Glop::Actor';

sub new { 
    my ($class, $p, $basecol, $keys) = @_;
    
    my $movespeed = 20;

    my ($kleft, $kright, $kup, $kdown) = @$keys;

    my $self = $class->SUPER::new;
    $self->{p} = $p;
    $self->{strength} = 0;
    $self->{color} = $basecol;

    A Glop::Floater sub {
        my $kb = Glop::Input->KeyState;
        if ($kb->$kleft)  { $self->{p} -= v(STEP * $movespeed, 0) }
        if ($kb->$kright) { $self->{p} += v(STEP * $movespeed, 0) }
        if (1)            { $self->{strength} = 0 }
        if ($kb->$kup)    { $self->{strength} = 1 }
        if ($kb->$kdown)  { $self->{strength} = -1 }
    };

    $GLOBAL{electrocuter}->add_source($self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        my @color;
        if ($self->{strength} > 0) {
            @color = (1,0,0);
        }
        elsif ($self->{strength} < 0) {
            @color = (0,0,1);
        }
        else {
            @color = @{$self->{color}};
        }
        glTranslate($self->{p}->list);
        glColor(@color);
        Glop::Draw->Circle(-radius => 2);
   };
};

sub position {
    my ($self) = @_;
    $self->{p};
}

sub field {
    my ($self, $pos) = @_;
    my $v = $pos - $self->{p};
    $self->{strength} * $v / $v->norm ** 2;
}

sub fsurface {
    my ($self, $pos) = @_;
    my $d = $pos - $self->{p};
    if ($d * $d < 0.1) {
        0;
    }
    else {
        $self->{strength} * log($d * $d);
    }
}

1;
