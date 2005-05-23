package Glop::Kernel;

use strict;

use Glop ();
use SDL ();
use Exporter;

our $DIDRUN = 0;

sub new {
    my ($class) = @_;
    my $self = bless {
        state => undef,
        last_frame => undef,
        frame_count => 0,
        frame_count_timestamp => 0,
        frame_rate => undef,
    } => ref $class || $class;
    $self;
}

sub run {
    my ($self, $code) = @_;
    
    $DIDRUN = 1;
    
    GLOP_KERNEL_MAIN_LOOP:
    while (1) {
        $_[0]->step($code);
    }
}

sub norun {
    $DIDRUN = 1;
}

END {
    unless ($DIDRUN) {
        warn "\$Glop::KERNEL->run never called\n";
    }
}

sub step {
    my ($self, $code) = @_;
    my $ctime = SDL::GetTicks();

    if ($self->{frame_count}++ == 60) {
        my $timediff = ($ctime - $self->{frame_count_timestamp}) / 1000;
        $self->{frame_rate} = $self->{frame_count} / $timediff;
        $self->{frame_count} = 0;
        $self->{frame_count_timestamp} = $ctime;
    }
    
    if (defined $self->{last_frame}) {
        $Glop::FSTEP = ($ctime - $self->{last_frame}) / 1000;
    }
    $self->{last_frame} = $ctime;

    package Glop::GLSpace;
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();

    $self->{state}->step;
    $self->{state}->draw;

    $code && $code->();
    
    $Glop::APP->sync;
}

sub frame_rate {
    my ($self) = @_;
    $self->{frame_rate};
}

sub add {
    my $self = shift;
    $self->{state}->add(@_);
}

sub remove {
    my $self = shift;
    $self->{state}->remove(@_);
}

sub heap {
    $_[0]->{state}->heap;
}

sub save_state {
    my ($self) = @_;
    $self->{state}->clone;
}

sub new_state {
    my ($self) = @_;
    my $ret = $self->{state};
    $self->{state} = Glop::Kernel::State->new;
    $self->setup_state;
    $ret;
}

sub setup_state {
    my ($self) = @_;

    Glop::Input->Key(
        escape => sub { $self->quit },
    );
}

sub switch_state {
    my ($self, $state) = @_;
    my $ret = $self->{state};
    $self->{state} = $state;
    $ret;
}

sub state {
    my ($self) = @_;
    $self->{state};
}

sub quit {
    last GLOP_KERNEL_MAIN_LOOP;
}

package Glop::Kernel::State;

use base 'Glop::Floater';

sub new {
    my ($class) = @_;
    my $self = $class->SUPER::new;
    $self->{live}  = [ {} ]; 
    $self->{heap}  = { };
    $self;
}

sub heap {
    $_[0]{heap};
}

sub clone {
    my ($self) = @_;
    bless {
        %$self
    } => ref $self;
}

sub compact {
    my ($self) = @_;
    my $live = $self->{live};
    my $new = [ {} ];
    
    for (1..$#$live) {
        if (my $o = $live->[$_]) {
            push @$new, $o;
            $new->[0]{$o} = $#$new;
        }
    }
    $self->{live} = $new;    
}

sub add {
    my ($self, @refs) = @_;
    my $live = $self->{live};
    for (@refs) {
        unless ($live->[0]{$_}) {  # don't add again if we're already in the set
            if (ref eq 'CODE') {
                require Glop::Actor::Anonymous;
                push @$live, Glop::Actor::Anonymous->new($_);
            }
            else {
                push @$live, $_;
                $live->[0]{$_} = $#$live;
            }
        }
    }
}

sub remove {
    my ($self, @refs) = @_;
    my $live = $self->{live};
    for (@refs) {
        undef $live->[$live->[0]{$_}];
        delete $live->[0]{$_};
    }
}

sub step {
    my ($self) = @_;
    my $live = $self->{live};
    my $undefs = 0;

    for (@$live[1..$#$live]) {
        $_ ? $_->step : $undefs++;
    }
    
    if ($undefs > @$live / 2) {
        $self->compact;
    }
}

sub draw {
    my ($self) = @_;
    my $live = $self->{live};

    for (@$live[1..$#$live]) {
        $_ && $_->draw;
    }
}

1;
