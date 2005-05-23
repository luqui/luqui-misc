#!/usr/bin/perl

use strict;
use FindBin;
use Perl6::Slurp;

use lib glob '/home/fibonaci/work/code/glop/blib/{lib,arch}';
our ($SCREEN_WIDTH, $SCREEN_HEIGHT);
BEGIN {
    $SCREEN_WIDTH = 1024;
    $SCREEN_HEIGHT = 768;
}
use Glop -view => [ 0, -0.5, 1, 0.5 ], '-fullscreen',
         -pixwidth  => $SCREEN_WIDTH,
         -pixheight => $SCREEN_HEIGHT,
         -step => 0.01;
use Glop::AutoGL;

use Ball;
use Boundary;
use ViewScreen;

glDisable(GL_DEPTH_TEST);
SDL::ShowCursor(0);

my @scores;
if (-e "$FindBin::Bin/scores") {
    @scores = map { [split /\s+/, $_, 2] } 
                slurp "$FindBin::Bin/scores", {chomp=>1};
}

sub mainmenu {
    $KERNEL->new_state;
    A Glop::Floater sub {
        preserve {
            glColor(1,1,1);
            glTranslate(0.5, 0, 0);
            Glop::Draw->Sprite("$FindBin::Bin/recursiverse.png");
        };
    };
    
    Glop::Agent->Menu(
        [ "Play" => sub { game() } ],
        [ "High scores" => sub { scorescreen() } ],
        [ "Quit" => sub { $KERNEL->quit } ],
        -size => 72,
    );
}

sub game {
    $KERNEL->new_state;
    my $player1 = ViewScreen->make(
                    screen => [ 0, 0, $SCREEN_WIDTH, $SCREEN_HEIGHT ]);
}

sub deadmenu {
    my ($score) = @_;
    $KERNEL->new_state;
    
    my $high;
    $high = "High " if $score > highscore();
    Glop::Agent->Menu(
        [ "${high}Score: " . int($score)  => sub { askscore($score) } ],
        [ "Try Again" => sub { game() } ],
        [ "Back"      => sub { mainmenu() } ],
        -size => 72,
    );
}

sub highscore {
    if (@scores > 4) {
        $scores[4][0];
    }
    else {
        0;
    }
}

sub askscore {
    my ($score) = @_;
    
    $KERNEL->new_state;
    A Glop::Floater sub {
        preserve {
            glTranslate(0.25, 0.2, 0);
            glScale(0.1, 0.1, 1);
            glColor(1,1,1);
            Glop::Draw->Text('Enter Name', -size => 72);
        };
    };

    Glop::Agent->InputBox(
        size => 72,
        predraw => sub {
            glTranslate(0.25, 0, 0);
            glScale(0.05, 0.05, 1);
            glColor(1,0,0);
        },
        enter => sub {
            enterscore($score, $_[0]);
        },
    );
}

sub enterscore {
    my ($score, $name) = @_;
    push @scores, [int $score, $name];
    @scores = sort { $b->[0] <=> $a->[0] } @scores;
    scorescreen();
}

sub scorescreen {
    $KERNEL->new_state;
    
    my @menu;
    for (@scores[0..(@scores >= 5 ? 4 : $#scores)]) {
        push @menu, [
            sprintf('%6d  %s', $_->[0], $_->[1]),
            sub { mainmenu() },
        ];
    }
    Glop::Agent->Menu(
        @menu,
        -size => 72,
        -font => "$FindBin::Bin/Vera.ttf",
    );
}

sub writescores {
    open my $fh, '>', "$FindBin::Bin/scores" or die "Couldn't open scores for writing: $!\n";
    for (@scores) {
        print $fh "$_->[0] \t$_->[1]\n";
    }
}

mainmenu();

$KERNEL->run;

writescores();
