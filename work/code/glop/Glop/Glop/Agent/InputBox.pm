package Glop::Agent::InputBox;

use strict;
use Glop ();
use Glop::Draw::Text;

use base 'Glop::Floater';

sub init {
    my ($self, %opt) = @_;

    $self->{predraw} = $opt{predraw} || sub { };
    $self->{onkey}   = $opt{onkey}   || sub { 1 };
    $self->{enter}   = $opt{enter}   || sub { };

    $self->{cursor}  = defined $opt{cursor} ? $opt{cursor} : '|';
    $self->{font}    = $opt{font}    || '';
    $self->{size}    = $opt{size}    || '';
    $self->{buffer}  = '';
    $self->{bufpos}  = 0;
    $self->{textobj} = undef;

    Glop::Input->KeyNames(sub {
        $self->handle(@_);
    });
}

sub handle {
    my ($self, $key) = @_;

    $self->{onkey}->($key, $self->{buffer}) or return;

    $key = ' ' if $key eq 'space';
    if (1 == length $key) {
        substr($self->{buffer}, $self->{bufpos}, 0) = $key;
        $self->{bufpos}++;
        undef $self->{textobj};
    }
    else {
        if ($key eq 'backspace') {
            if ($self->{bufpos}) {
                substr($self->{buffer}, $self->{bufpos}-1, 1) = '';
                $self->{bufpos}--;
                undef $self->{textobj};
            }
        }
        elsif ($key eq 'delete') {
            substr($self->{buffer}, $self->{bufpos}, 1) = '';
            undef $self->{textobj};
        }
        elsif ($key eq 'left') {
            if ($self->{bufpos} > 0) { 
                $self->{bufpos}--; 
                undef $self->{textobj};
            }
        }
        elsif ($key eq 'right') {
            if ($self->{bufpos} < length($self->{buffer})) {
                $self->{bufpos}++;
                undef $self->{textobj};
            }
        }
        elsif ($key eq 'return') {
            $self->{bufpos} = length($self->{buffer});
            undef $self->{textobj};
            $self->{enter}->($self->{buffer});
        }
    }
}

sub draw {
    my ($self) = @_;

    package Glop::GLSpace;
    glPushMatrix();
    $self->{predraw}->();

    unless ($self->{textobj}) {
        my $buf = substr($self->{buffer}, 0, $self->{bufpos}) . 
                  $self->{cursor} . 
                  substr($self->{buffer}, $self->{bufpos});
        $self->{textobj} = Glop::Draw::Text->new(
            $buf,
            ($self->{font} ? (-font => $self->{font}) : ()),
            ($self->{size} ? (-size => $self->{size}) : ()),
        );
    }

    $self->{textobj}->draw;
    
    glPopMatrix();
}

1;
