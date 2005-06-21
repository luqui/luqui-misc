package Glop::Agent::Menu;

use strict;

use Glop ();
use Glop::Draw::Text;

use base 'Glop::Floater';

sub new {
    my ($class, @items) = @_;

    my $self = $class->SUPER::new;
    my %outopt;

    for (my $i = 0; $i < @items; $i++) {
        if ($items[$i] =~ /^-/) {
            $outopt{$items[$i]} = $items[$i+1];
            splice @items, $i, 2;
            $i--;
        }
    }
    
    my @menu = map {
        my ($text, $code, %inopt) = @$_;
        my %fontopt = (
            -size => 72,
        );
        $outopt{$_} and $fontopt{$_} = $outopt{$_} for qw{-font -size};
        $inopt{$_}  and $fontopt{$_} = $inopt{$_}  for qw{-font -size};
        my $textobj = Glop::Draw::Text->new($text, %fontopt);
        {
            text => $text,
            code => $code,
            textobj => $textobj,
            height => $textobj->height,
            width => $textobj->width,
            %outopt,
            %inopt,
        }
    } @items;

    $self->{menu} = \@menu;
    $self->{opt}  = \%outopt;
    $self->{sel}  = 0;
    $self;
}

sub init {
    my ($self) = @_;
    my $opt = $self->{opt};

    Glop::Input->Key(
        $opt->{upkey}   || up     => sub { $self->{sel}--; $self->{sel} %= @{$self->{menu}} },
        $opt->{downkey} || down   => sub { $self->{sel}++; $self->{sel} %= @{$self->{menu}} },
        $opt->{selkey}  || return => sub {
            $self->{menu}[$self->{sel}]{code}->();
        },
    );

    $self;
}

sub draw {
    my ($self) = @_;

    my $height = 0;
    $height += $_->{height} for @{$self->{menu}};
    my $width = 0;
    $_->{width} > $width and $width = $_->{width} for @{$self->{menu}};
    
    package Glop::GLSpace;
    glMatrixMode(GL_PROJECTION);
    glPushMatrix();
    glLoadIdentity();
    Glop::view(-$width, -$height, 2*$width, 2*$height);
    glMatrixMode(GL_MODELVIEW);
    glPushMatrix();
    glLoadIdentity();
    
    for my $i (reverse 0..$#{$self->{menu}}) {
        if ($i == $self->{sel}) {
            my @color = @{$self->{menu}[$i]{-selcolor} || [ 1,1,0 ]};
            glColor(@color);
        }
        else {
            my @color = @{$self->{menu}[$i]{-color} || [ 1,1,1 ]};
            glColor(@color);
        }
        $self->{menu}[$i]{textobj}->draw;
        glTranslate(0,1,0);
    }

    glPopMatrix();
    glMatrixMode(GL_PROJECTION);
    glPopMatrix();
    glMatrixMode(GL_MODELVIEW);
}

1;
