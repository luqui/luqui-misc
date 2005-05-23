package Evaluator;

use strict;
use Glop::AutoGL;
use Math::Complex;

my @names;
BEGIN { @names = qw{tan Re Im arg e pi step} }

sub mod_import {
    no strict 'refs';
    my $package = caller;
    for (@names) {
        *{"$package\::$_"} = \&$_;
    }
}

sub tan {
    my ($arg) = @_;
    sin($arg)/cos($arg);
}

BEGIN { 
    *Re  = \&Math::Complex::Re;
    *Im  = \&Math::Complex::Im;
}

sub arg {
    if (ref $_[0]) {
        Math::Complex::arg($_[0]);
    }
    else {
        0;
    }
}

sub step {
    $_[0] < 0 ? 0 : 1;
}

sub e() { exp(1) }

sub pi() { 4*atan2 1,1 }

package Evaluator::Function;

use Glop;
use Math::Complex;

BEGIN {
    Evaluator::mod_import();
}

sub new {
    my ($class, $eqs) = @_;

    return unless $eqs;
    
    my $code = <<EOC;
    sub {
        for (my \$x = -16; \$x < 16; \$x += 1/16) {
            eval {
                my \$yv = ($eqs->[0][1]);
                unless (ref \$yv && \$yv->Im) {  # only plain old numbers please
                    push \@points, [ \$x, \$yv ];
                }
            };
        }
    }
EOC
    my @points;
    my $eval = eval $code;
    if ($eval) {
        $eval->();
        bless {
            points => \@points,
        } => ref $class || $class;
    }
    else {
        undef;
    }
}

sub points {
    my ($self) = @_;
    $self->{points};  # yes, an arrayref
}

sub draw {
    my ($self) = @_;
    glBegin(GL_LINE_STRIP);
    for (@{$self->{points}}) {
        glVertex(@$_);
    }
    glEnd();
}

1;
