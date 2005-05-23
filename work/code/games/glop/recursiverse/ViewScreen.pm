package ViewScreen;

use strict;

use Glop;
use Glop::AutoGL;
use Glop::Draw::Text;
use Carp;
use POSIX qw<fmod floor ceil>;
use base 'Glop::Floater';

use Ball;
use Boundary;
use Perl6::Attributes;

my $BALL_XPOS = 47;
my $BOUNDARY_WIDTH = 500;
my $HEIGHT = 80;

my $VIEWPORT_WIDTH = 100;
my $VIEWPORT_XPOS = 40;

my $FIELD_EXP_CONSTANT = exp(1);
my $FIELD_EXP_OFFSET = 50;

my $RADIUS_CONSTANT = 0.056;
my $EXAGGERATION_CONSTANT = 1;

my $GOD_MODE = 0;

my $COLLIDE_LEEWAY = 0.25;

my $PULSE = 1;
my $SHORTPULSE = 71;

my $MOMENTUM_RATE = 0.5;

SDL::ShowCursor(0);

sub init {
    my ($self, %options) = @_;
    my $ball = Ball->new;
    $.screen   = $options{screen} || croak 'No screen supplied, dumbshit';
    $.ball     = $ball;
    my $rad = $RADIUS_CONSTANT * $ball->momentum;
    $.boundary = Boundary->new($BOUNDARY_WIDTH, 0, $rad);
    $.ballvel  = 0;
    $.campos   = 0;
    $.height   = $HEIGHT * $.screen[3] / $::SCREEN_HEIGHT;
    $.radius   = $.height / 3;
    $.center   = 0;
    $.offset   = 0;
    $.nextframe = 0;
    $.pulse = $PULSE;
    $.shortpulse = $SHORTPULSE;
    $.score = 0;
    $.scoretext;
    $.scorecount = 0;
    $self;
}

sub step {
    my ($self) = @_;
    $.pulse -= STEP;
    $.shortpulse -= $.ball->velocity * STEP;
    $.nextframe -= STEP;
    while ($.nextframe <= 0) {
        my $center = $EXAGGERATION_CONSTANT * $.ball->ypos;
        my $radius = $RADIUS_CONSTANT * $.ball->momentum;
        $.boundary->advance($center, $radius);
        $.nextframe += 1 / $.ball->velocity;
    }
    $.offset = $.nextframe * $.ball->velocity;
    #$.score += sqrt($.ball->velocity**2 + $.ballvel**2) * STEP;
    $.score += 100 * STEP;

    while ($.shortpulse <= 0) {
        my $x = $VIEWPORT_XPOS + $VIEWPORT_WIDTH;
        my ($center, $radius) = ($.ball->ypos, $.ball->size);
        $.boundary->make_image($x, $center, $radius, [ 0, 0, 1 ], 0);
        $.shortpulse += $SHORTPULSE;
    }
    while ($.pulse <= 0) {
        $.boundary->make_image(-1, $.ball->ypos, $.ball->size, [ 1, 0, 0 ], 1);
        $.pulse += $PULSE;
    }

    $.ballvel = 0;
    Glop::Input->KeyState->w && do { $.ball->move(30); $.ballvel = 30 };
    Glop::Input->KeyState->s && do { $.ball->move(-30); $.ballvel = -30 };
    Glop::Input->KeyState->d && $.ball->grow(-4);
    Glop::Input->KeyState->a && $.ball->grow(4);
    
    $.ball->add_momentum($MOMENTUM_RATE);

    $.campos = $.ball->ypos;

    unless ($GOD_MODE) {
        my ($center, $radius) = $.boundary->slice($BALL_XPOS);

        if ($center < $radius) {
            if ($.ball->ypos - $.ball->size < -$center - $radius) {
                goto DIE;
            }
            if ($.ball->ypos + $.ball->size > $center + $radius) {
                goto DIE;
            }
        }
        else {
            if (abs($.ball->ypos) + $.ball->size > $center + $radius
             || abs($.ball->ypos) - $.ball->size < $center - $radius) {
                 goto DIE;
            }
        }
        for my $i (floor($BALL_XPOS-$.ball->size)..ceil($BALL_XPOS+$.ball->size)) {
            if (my $image = $.boundary->image($i)) {
                if ($image->{doubled}) {
                    if (($BALL_XPOS - $i) ** 2 + (abs($.ball->ypos) - abs($image->{center})) ** 2 
                          < ($.ball->size + $image->{radius} - $COLLIDE_LEEWAY) ** 2) {
                              goto DIE;
                    }
                }
                else {
                    if (($BALL_XPOS - $i) ** 2 + ($.ball->ypos - $image->{center}) ** 2 
                          < ($.ball->size + $image->{radius} - $COLLIDE_LEEWAY) ** 2) {
                              goto DIE;
                    }
                }
            }
        }
        return;

        DIE: {
            $self->kill;
            ::deadmenu($.score);
        }
    }
}

sub draw {
    my ($self) = @_;
    glViewport(@.screen);
    $self->draw_map();
    $self->draw_field();
    $self->draw_score();
}

sub draw_score {
    my ($self) = @_;
    if (!$.scoretext || $.scorecount++ % 10 == 0) {
        $.scoretext = Glop::Draw::Text->new(int($.score));
    }
    preserve {
        glTranslate(0.8, 0.4, 0);
        glScale(0.05, 0.05, 1);
        glColor(1, 1, 1);
        $.scoretext->draw if $.scoretext;
    };
}

sub draw_boundary {
    my ($self, $x0, $xf) = @_;
    
    $.center = $.ball->ypos;
    
    glBegin(GL_LINES);
    for my $i ($x0+1..$xf-1) {
        my ($centera, $radiusa) = $.boundary->slice($i-1);
        my ($centerb, $radiusb) = $.boundary->slice($i);

        glVertex($i + $.offset,      $centera + $radiusa);
        glVertex($i + $.offset + 1,  $centerb + $radiusa);
        glVertex($i + $.offset,     -$centera - $radiusa);
        glVertex($i + $.offset + 1, -$centerb - $radiusa);

        if ($centerb > $radiusb) {
            if ($centera > $radiusa) {
                glVertex($i + $.offset, $centera - $radiusa);
            }
            else {
                glVertex($i + $.offset, 0);
            }
            glVertex($i + $.offset + 1, $centerb - $radiusb);
            
            if ($centera > $radiusa) {
                glVertex($i + $.offset, -($centera - $radiusa));
            }
            else {
                glVertex($i + $.offset, 0);
            }
            glVertex($i + $.offset + 1, -($centerb - $radiusb));
        }
    }
    glEnd();

    glLineWidth(1.0);
    for my $i ($x0..$xf-1) {
        my ($top, $bottom) = $.boundary->slice($i);
        if (my $image = $.boundary->image($i)) {
            preserve {
                glColor(@{$image->{color}});
                glTranslate($i + $.offset, $image->{center}, 0);
                Glop::Draw->Circle(-radius => $image->{radius});
                if ($image->{doubled}) {
                    glTranslate(0, -2 * $image->{center}, 0);
                    Glop::Draw->Circle(-radius => $image->{radius});
                }
            };
        }
        glColor(0.2, 0.4, 0.2);
        #glBegin(GL_LINES);
        #if ($.boundary->line($i)) {
        #    glVertex($i + $.offset, $top);
        #    glVertex($i + $.offset, $bottom);
        #}
        #glEnd();
    }
    
    #for (my $j = 0.2; $j < 1; $j += 0.2) {
        #glBegin(GL_LINE_STRIP);
        #for (my $i = $x0; $i < $xf; $i += 4) {
        #    my ($top, $bottom) = $.boundary->slice($i+1);
        #    glVertex($i + $.offset, $bottom + ($top - $bottom) * $j);
        #}
        #glEnd();
    #}
}

sub draw_exp_boundary {
    my ($self, $x0, $xf) = @_;
    my $pow = $FIELD_EXP_CONSTANT;
    my $x0s = $x0 + $FIELD_EXP_OFFSET;
    my $f = sub { 
        my ($x, $drawstart) = @_; 
        if ($x - $x0s + 1 >= 1) {
            my $xx = log($x - $x0s + 1) ** $pow * ($xf - $x0s) / log($xf - $x0s + 1) ** $pow + $x0s;
            glVertex($xx, $drawstart);
        }
    };
        
    glBegin(GL_LINES);
    for (my $i = $x0+2; $i < $xf; $i += 3) {
        my ($centera, $radiusa) = $.boundary->slice($i-1);
        my ($centerb, $radiusb) = $.boundary->slice($i);

        $f->($i + $.offset,      $centera + $radiusa);
        $f->($i + $.offset + 1,  $centerb + $radiusa);
        $f->($i + $.offset,     -$centera - $radiusa);
        $f->($i + $.offset + 1, -$centerb - $radiusa);

        if ($centerb > $radiusb) {
            if ($centera > $radiusa) {
                $f->($i + $.offset, $centera - $radiusa);
            }
            else {
                $f->($i + $.offset, 0);
            }
            $f->($i + $.offset + 1, $centerb - $radiusb);
            
            if ($centera > $radiusa) {
                $f->($i + $.offset, -($centera - $radiusa));
            }
            else {
                $f->($i + $.offset, 0);
            }
            $f->($i + $.offset + 1, -($centerb - $radiusb));
        }
    }
    glEnd();
}

sub draw_map {
    my ($self) = @_;
    preserve {
        glLineWidth(1.0);
        glScale(1/$BOUNDARY_WIDTH, 0.5/$.radius, 1);
        glTranslate(1/$BOUNDARY_WIDTH, -$.center, 1);
        glColor(1,1,1);
        $self->draw_exp_boundary(0, $BOUNDARY_WIDTH);
    };
}

sub draw_field {
    my ($self) = @_;
    preserve {
        glScale(1/$VIEWPORT_WIDTH, 0.5/$.radius, 1);
        glTranslate(-$VIEWPORT_XPOS, -$.center, 0);

        glColor(0,1,0);
        glLineWidth(5.0);
        $self->draw_boundary($VIEWPORT_XPOS-1, $VIEWPORT_WIDTH + $VIEWPORT_XPOS+1);

        $self->draw_ball();
    };
}

sub draw_ball {
    my ($self) = @_;

=begin comment
    preserve {
        glTranslate($BALL_XPOS, $.ball->ypos, 0);
        glColor(1,0,0);
        Glop::Draw->Circle(-radius => $.ball->size);
    };
=cut

    preserve {
        glEnable(GL_BLEND);
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
        glTranslate($BALL_XPOS, $.ball->ypos, 0);
        for (my $i = 0.1; $i < 1; $i += 0.4) {
            preserve {
                glScale($.ball->velocity/20/$i, 1, 1);
                glColor(1, 0, 0, $i);
                Glop::Draw->Circle(-radius => $.ball->size);
            };
        }
        glDisable(GL_BLEND);
        glColor(0,0,0);
        Glop::Draw->Circle(-radius => $.ball->size);
    }
}

1;
