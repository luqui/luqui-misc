package Widget;

use Glop::AutoGL;
use strict;

use base 'Glop::Actor';

package Widget::LineCharge;
use POSIX qw{atan};

use Glop;

use base 'Widget';

our %GLOBAL;
BEGIN { *GLOBAL = \%::GLOBAL }

sub new {
    my ($class, $pos, $norm, $length, $lambda) = @_;

    my $self = $class->SUPER::new;
    $self->{pos}    = $pos;
    $self->{norm}   = $norm / $norm->norm;
    $self->{length} = $length/2;
    $self->{lambda} = $lambda;

    $GLOBAL{electrocuter}->add_static_source($self);
    $self;
}

sub draw {
    my ($self) = @_;
    my $n = $self->{norm};
    preserve {
        glTranslate($self->{pos}->list);
        glRotate(180 / 3.1415 * atan2($n->x, $n->y), 0, 0, 1);
        if ($self->{lambda} > 0) {
            glColor(1,0,0);
        }
        else {
            glColor(0,0,1);
        }
        glLineWidth(2.0);
        glBegin(GL_LINES);
            glVertex(-$self->{length}, 0, 0);
            glVertex($self->{length}, 0, 0);
        glEnd();
    };
}

sub field {
    my ($self, $pos) = @_;
    my $p = $pos - $self->{pos};
    my $j = $self->{norm};
    my $i = v($j->y, -$j->x);

    my $x = $p*$i;
    my $y = $p*$j;
    my $l = $self->{length};

    # Inverse
    my $disca = $l*$l + 2*$x*$l + $x*$x + $y*$y;
    my $discb = $l*$l - 2*$x*$l + $x*$x + $y*$y;
    my $ic;
    if ($disca > 0 && $discb > 0) {
        $ic = 0.5 * (log($disca) - log($discb));
    }
    else {
        $ic = 0;
    }
                        
    my $jc = atan(($l-$x) / $y) - atan((-$l-$x) / $y);

    $self->{lambda} * $self->{length} * ($ic * $i + $jc * $j);
}

sub fsurface {
    my ($self, $pos) = @_;
    my $p = $pos - $self->{pos};
    my $j = $self->{norm};
    my $i = v($j->y, -$j->x);
    my $x = $p * $i;
    my $y = $p * $j;
    my $l = $self->{length};
    
    my $disca = ($l - $x)**2 + $y*$y;
    my $discb = ($l + $x)**2 + $y*$y;
    if ($disca > 0 && $discb > 0) {
        $self->{lambda} * $l *
        1.5 * (2 * $y * (atan(($l-$x) / $y) + atan(($l + $x) / $y)) +
               ($l - $x) * log($disca) +
               ($l + $x) * log($discb));
    }
    else {
        0;
    }
}

package Widget::Wall;

use Glop;
use base 'Widget';

sub new {
    my ($class, $pos, $norm) = @_;
    my $self = $class->SUPER::new;
    $self->{pos} = $pos;
    $self->{norm} = $norm;

    ODE::Geom::Plane->new($GLOBAL{collision_space}, $pos, $norm);
    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glRotate(180 / 3.1415 * atan2($self->{pos}->x, $self->{pos}->y), 0, 0, 1);
        glColor(1,1,1);
        glLineWidth(2.0);
        glBegin(GL_LINES);
            glVertex(-100, 0, 0);
            glVertex( 100, 0, 0);
        glEnd();
    };
}

package Widget::DeathWall;

use Glop;
use base 'Widget';

use Class::Multimethods;

multimethod collide => qw(Ball Widget::DeathWall) => sub {
    push @::SCHED, sub { ::single_level($::GLOBAL{level}) };
};

multimethod collide => qw(Widget::DeathWall Ball) => sub {
    collide(@_[1,0]);
};

multimethod collide => qw(Widget Block) => sub { { } };

multimethod collide => qw(Block Widget) => sub { { } };

sub new {
    my ($class, $pos, $norm) = @_;
    my $self = $class->SUPER::new;
    $self->{pos} = $pos;
    $self->{norm} = $norm;

    my $geom = ODE::Geom::Plane->new($GLOBAL{collision_space}, $pos, $norm);
    $::GLOBAL{collider}->register($geom => $self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glRotate(180 / 3.1415 * atan2($self->{pos}->x, $self->{pos}->y), 0, 0, 1);
        glColor(0,0.4,0);
        glLineWidth(2.0);
        glBegin(GL_LINES);
            glVertex(-100, 0, 0);
            glVertex( 100, 0, 0);
        glEnd();
    };
}

package Widget::SideWall;

use Glop;
use base 'Widget';

use Class::Multimethods;

multimethod collide => qw(Ball Widget::SideWall) => sub {
    $_[1]->{side} += $::GLOBAL{side};
    if (abs($_[1]->{side}) >= 3) {
        if ($::GLOBAL{side} < 0) {
            $::GLOBAL{Lscore}++;
        }
        else {
            $::GLOBAL{Rscore}++;
        }
        $::GLOBAL{side} = $_[1]->{side} = 0;
    }
    { };
};

multimethod collide => qw(Widget::SideWall Ball) => sub {
    collide(@_[1,0]);
};

sub new {
    my ($class, $pos, $norm) = @_;
    my $self = $class->SUPER::new;
    $self->{pos} = $pos;
    $self->{norm} = $norm;
    $self->{side} = 0;

    my $geom = ODE::Geom::Plane->new($GLOBAL{collision_space}, $pos, $norm);
    $::GLOBAL{collider}->register($geom => $self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glRotate(180 / 3.1415 * atan2($self->{pos}->x, $self->{pos}->y), 0, 0, 1);
        if ($self->{side} < 0) {
            glColor(1,1,0);
        }
        elsif ($self->{side} > 0) {
            glColor(0,1,0);
        }
        else {
            glColor(0,0,0);
        }
        if (abs($self->{side}) > 1) {
            glLineWidth(8.0);
        }
        else {
            glLineWidth(2.0);
        }
        glBegin(GL_LINES);
            glVertex(-100, 0, 0);
            glVertex( 100, 0, 0);
        glEnd();
    };
}

package Widget::BackWall;

use Glop;
use base 'Widget';

use Class::Multimethods;

multimethod collide => qw(Ball Widget::BackWall) => sub {
    if ($::GLOBAL{side} > 0) { $::GLOBAL{side} = -1 }
    else { $::GLOBAL{side} = 1 }
    { };
};

multimethod collide => qw(Widget::BackWall Ball) => sub {
    collide(@_[1,0]);
};

sub new {
    my ($class, $pos, $norm) = @_;
    my $self = $class->SUPER::new;
    $self->{pos} = $pos;
    $self->{norm} = $norm;
    $self->{side} = 0;

    my $geom = ODE::Geom::Plane->new($GLOBAL{collision_space}, $pos, $norm);
    $::GLOBAL{collider}->register($geom => $self);

    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{pos}->list);
        glRotate(180 / 3.1415 * atan2($self->{pos}->x, $self->{pos}->y), 0, 0, 1);
        if ($::GLOBAL{side} < 0) {
            glColor(1,1,0);
        }
        elsif ($::GLOBAL{side} > 0) {
            glColor(0,1,0);
        }
        else {
            glColor(0,0,0);
        }
        glLineWidth(2.0);
        glBegin(GL_LINES);
            glVertex(-100, 0, 0);
            glVertex( 100, 0, 0);
        glEnd();
    };
}

package Widget::ScoreReport;

use Glop;
use base 'Widget';

sub new {
    my ($class) = @_;
    
    my $self = $class->SUPER::new;
    $self->{prev} = [0, 0];
    $self->{cache} = [ Glop::Draw::Text->new("0", -size => 72),
                       Glop::Draw::Text->new("0", -size => 72) ];
    $self;
}

sub draw {
    my ($self) = @_;
    preserve {
        unless ($::GLOBAL{Lscore} == $self->{prev}[0]) {
            $self->{prev}[0] = $::GLOBAL{Lscore};
            $self->{cache}[0] = Glop::Draw::Text->new($::GLOBAL{Lscore}, -size => 72);
        }
        glTranslate(-30, 40, 0);
        glColor(1,1,0);
        glScale(6,6,1);
        $self->{cache}[0]->draw;
    };
    preserve {
        unless ($::GLOBAL{Rscore} == $self->{prev}[1]) {
            $self->{prev}[1] = $::GLOBAL{Rscore};
            $self->{cache}[1] = Glop::Draw::Text->new($::GLOBAL{Rscore}, -size => 72);
        }
        glTranslate(20, 40, 0);
        glColor(0,1,0);
        glScale(6,6,1);
        $self->{cache}[1]->draw;
    };
}

package Widget::EFieldControl;

use Glop;
use base 'Widget';

sub new {
    my ($class, $amount) = @_;
    
    my $self = $class->SUPER::new;
    $self->{amount}    = $amount;
    $self->{dir} = v(0,0);

    Glop::Input->Key(
        '-keydown',
            w => sub { $self->{dir} += v(0, $amount) },
            s => sub { $self->{dir} += v(0, -$amount) },
            a => sub { $self->{dir} += v(-$amount, 0) },
            d => sub { $self->{dir} += v($amount, 0) },
        '-keyup',
            w => sub { $self->{dir} -= v(0, $amount) },
            s => sub { $self->{dir} -= v(0, -$amount) },
            a => sub { $self->{dir} -= v(-$amount, 0) },
            d => sub { $self->{dir} -= v($amount, 0) },
    );
    
    $GLOBAL{electrocuter}->add_static_source($self);

    $self;
}

sub field {
    my ($self, $pos) = @_;
    $self->{dir};
}

1;
