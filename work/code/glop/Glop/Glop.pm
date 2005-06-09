package Glop;

use 5.006;
use strict;
no warnings;

package Glop;

use Exporter;
use base 'Exporter';

use ODE;
use SDL;
use SDL::App;
use SDL::Event;
use SDL::OpenGL ();
use Carp;

our $SORT;
our $FSTEP = 0.05;
our $REALSTEP = 0.05;  # for people who missed the optimization
# This is only a temporary definition until import is called
sub STEP () { $REALSTEP }

our @ISA = qw(Exporter);
our %EXPORT_TAGS;
BEGIN {
    $EXPORT_TAGS{lang} = [ qw{v drawing preserve invar STEP $KERNEL view} ];
    $EXPORT_TAGS{util} = [ qw{within_box zorder} ];
    $EXPORT_TAGS{all} = [ 
        '$FSTEP',
        map { @$_ } @EXPORT_TAGS{qw{lang util}} 
    ];
    $EXPORT_TAGS{gl} = [ ];  # This isn't what it looks like.  See import below.

    our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );
}

our $VERSION = '0.01';

our $APP;
my $init_args;

sub process_options {
    my %noarg = (
        -quiet      => 1,
        -fullscreen => 1,
        -resizable  => 1,
        -noinit     => 1,
        -sort       => 1,
    );
    
    my %opt;

    while (my $opt = shift) {
        croak "Encountered non-option '$opt' in option position" unless $opt =~ /^-/;
        if ($noarg{$opt}) {
            $opt{$opt} = 1;
        }
        else {
            $opt{$opt} = shift;
        }
    }

    %opt;
}

sub import {
    my $package = shift;

    my $export;
    my $export_gl;

    if (lc $_[0] eq ':all') {
        shift;
        $export = [':all'];
    }

    my %opt = process_options @_;
    
    my $doinit;
    if (caller eq 'main') {
        $init_args = [ @_ ] unless $opt{-noinit};
        $doinit = 1;
    }
    if ($opt{-init}) {
        $init_args->{$_} = $opt{-init}{$_} for keys %{$opt{-init}};
        $doinit = 1;
    }
    
    if ($doinit) {
        if ($opt{-step}) {  # While I'd love to put this in init, this 
                            # must be done NOW
            if ($opt{-step} eq 'variable') {
                *STEP = sub () { $FSTEP };
                *REALSTEP = \$FSTEP;
            }
            elsif ($opt{-step} =~ s/x$//) {
                my $ostep = $opt{-step};
                *STEP = sub () { $ostep * $FSTEP };
                *REALSTEP = \($ostep * $FSTEP);
            }
            else {
                # If a fixed step is given, then STEP will be inlined to 
                # that value.
                my $step = $opt{-step};
                *STEP = sub () { $step };
                $REALSTEP = $step;
            }
        }
        else {
            *STEP = sub () { $FSTEP };
            *REALSTEP = \$FSTEP;
        }
    }
    
    if ($opt{-export}) {
        $export = $opt{-export};
    }

    if ($export) {
        if (grep { lc eq ':all' || lc eq ':gl' } @$export) {
            $export_gl = 1;
        }
        $package->export_to_level(1, $package, @$export);
    }
    else {
        $package->export_to_level(1, $package, ':lang');
    }

    if ($export_gl) {
        SDL::OpenGL->export_to_level(1, 'SDL::OpenGL');
    }

}

=begin comment

Internal package for extensions that don't want to eat all your memory filling
their symbol table with the many, many exported symbols of OpenGL.

For example:

    package Glop::Draw::Square;

    sub draw {
        package Glop::GLSpace;

        glBegin(GL_QUADS);
            glVertex(0,0);
            glVertex(1,0);
            glVertex(1,1);
            glVertex(0,1);
        glEnd();
    }

See Glop::AutoGL for an even cleaner (unless you have something against
source filters :-) alternative.

=end comment
=cut

BEGIN {
    *Glop::GLSpace:: = \%SDL::OpenGL::;
}

package Glop;

use Glop::Hacks;
use Glop::Floater;
use Glop::Kernel;
use Glop::Role;
use Glop::Draw;
use Glop::DisplayList;
use Glop::TransientQueue;
use Glop::Transient;
use Glop::Input;
use Glop::Actor;
use Glop::Agent;
use Glop::Texture;
use Glop::Physics;

our $KERNEL ||= Glop::Kernel->new;
$KERNEL->new_state;

sub init {
    my $package = shift;

    my %opt = process_options @_;

    my %sdlinit = map { $_, $opt{$_} } 
                  grep { exists $opt{$_} }
                  qw{ -title -icon_title -icon -resizable };

    $sdlinit{-width} = $opt{-pixwidth} || 1024;
    $sdlinit{-height} = $opt{-pixheight} || 768;

    my $olderr;
    if ($opt{-quiet} || 1) { # XXX
        open $olderr, '>&', \*STDERR;
        open STDERR, '>', undef;
    }
    
    $APP = SDL::App->new(
                %sdlinit,
               -flags => SDL_OPENGL | ($opt{-fullscreen} ? SDL_FULLSCREEN : 0),
           );
    
    if ($opt{-quiet} || 1) { # XXX
        open STDERR, '>&', $olderr;
    }

    $SORT = $opt{-sort};

    $opt{-view} ||= [ -1, -1, 1, 1 ];  # default to the biunit square
    view(@{$opt{-view}});
    
    package Glop::GLSpace;

    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);
    
    package Glop;
}

sub view {
    package Glop::GLSpace;
    my @view = @_;
    glMatrixMode(GL_PROJECTION);
        glLoadIdentity();
        if (@view == 4) { # 2D
            gluOrtho2D(@view[0,2,1,3]);
        }
        elsif (@view == 2 || @view == 3) { # 3D
            my ($eye, $center, $up) = map { Glop::v(@$_) } @view;
            if ($up == Glop::v()) {
                $up = ($center - $eye) x Glop::v(1,0,0);
                if ($up == 0) {  # ugh
                    $up = ($center - $eye) x Glop::v(0,1,0);
                }
            }
            gluPerspective(45, 4/3, 0.1, 100);
            gluLookAt(@$eye, @$center, @$up);
        }
        else {
            Carp::croak("Invalid view parameter");
        }
    glMatrixMode(GL_MODELVIEW);
}

INIT { __PACKAGE__->init(@$init_args) if $init_args; }

package Glop;

sub v {
    ODE::Vector->new(@_);
}

sub preserve(&) {
    Glop::GLSpace::glPushMatrix();
    my $ret = $_[0]->();
    Glop::GLSpace::glPopMatrix();
    $ret;
}

sub drawing(&) {
    my $ret = Glop::DisplayList->new->record;
    $_[0]->();
    $ret->done;
}

sub zorder($) {
    my ($z) = @_;
    Glop::GLSpace::glTranslate(0, 0, $z);
}

{
    my %invar;
    sub invar(&) {
        my $id = join $;, caller;
        if ($invar{$id}) {
            $invar{$id}->draw;
        }
        else {
            package Glop::GLSpace;
            my $list = Glop::DisplayList->new->record('execute');
            $_[0]->($list);
            $list->done;
            $invar{$id} = $list;
        }       
        $invar{$id};
    }
}

sub within_box {
    my ($v, $ll, $ur) = @_;
    $ll->x <= $v->x && $v->x <= $ur->x &&
    $ll->y <= $v->y && $v->y <= $ur->y &&
    $ll->z <= $v->z && $v->z <= $ur->z;
}

package ODE::Vector;
# Amend ODE::Vector's interface

use POSIX qw{floor};

sub quantize {
    my ($self, $q) = @_;
    $q ||= 1;
    if (ref $q) {
        ODE::Vector->new(
            ($q->x ? floor($self->x / $q->x) * $q->x : $self->x),
            ($q->y ? floor($self->y / $q->y) * $q->y : $self->y),
            ($q->z ? floor($self->z / $q->z) * $q->z : $self->z),
        );
    }
    else {
        ODE::Vector->new(
            floor($self->x / $q) * $q,
            floor($self->y / $q) * $q,
            floor($self->z / $q) * $q,
        );
    }
}


1;

=head1 NAME

Glop - Game Language Of Perl

=head1 SYNOPSIS

    use Glop qw{ :all };
    
    my $position = v(1,2);       # Create a 2D point/vector
    my $normal = v(1,2,3);       # Create a 3D point/vector
    # See ODE::Vector for the rest of this interface
    
    glBegin(GL_LINES);           # use OpenGL commands
        glVertex(@$position);    # use vectors as arrayrefs 
        glVertex(@$normal);
    glEnd();
    
    preserve {                   # surround in glPush/PopMatrix
        glTranslate(1,0,0);
        # ...
    };
    # translated back

    my $list = drawing {         # create a display list
        # OpenGL commands ...
    };
    $list->draw;                 # draw the list

    # Check that (0,0) is in the box from (-1,-1) to (1,1)
    within_box(v(0,0), v(-1,-1), v(1,1)) or die;

    # Use it in 3D
    within_box(v(0,1,1), v(0,0,0), v(2,2,2)) or die;
