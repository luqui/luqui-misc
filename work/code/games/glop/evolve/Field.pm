package Field;

use strict;
use Organism;
use Glop;
use Glop::AutoGL;

sub _modkey {
    my ($key, $code, $text) = @_;
    Glop::Input->Key(
        $key => sub {
            my $val = $code->();
            Timed Glop::Floater 1 => sub {
                preserve {
                    glColor(1,1,1);
                    glTranslate(50,75,0.5);
                    glScale(25,25,1);
                    Glop::Draw->Text("$text: $val");
                };
            };
        },
    );          
}

sub new {
    my ($class, $width, $height) = @_;

    my @data;
    for my $i (0..$width-1) {
        for my $j (0..$height-1) {
            $data[$i][$j] = { 
                exists => 1,
                food => 3,
            };
        }
    }

    $data[70][70]{food} = 10_000; # eden

    my $self = bless {
        keyorder => [ qw{ exists food } ],
        width => $width,
        height => $height,
        data => \@data,
        organisms => [ ],
        stepno => 0,
        resource => 20,
        cap => 5,
        ydisp => 0,
        xdisp => 0,
        total_food => 0,
    } => ref $class || $class;

    _modkey(g => sub { --$self->{resource} }, "Resources");
    _modkey(h => sub { ++$self->{resource} }, "Resources");
    _modkey(c => sub { --$self->{cap} }, "Cap");
    _modkey(v => sub { ++$self->{cap} }, "Cap");

    _modkey(w => sub { $self->{ydisp} =  1 }, "Ydisp");
    _modkey(s => sub { $self->{ydisp} =  0 }, "Ydisp");
    _modkey(x => sub { $self->{ydisp} = -1 }, "Ydisp");
    _modkey(d => sub { $self->{xdisp} =  1 }, "Xdisp");
    _modkey(s => sub { $self->{xdisp} =  0 }, "Xdisp");
    _modkey(a => sub { $self->{xdisp} = -1 }, "Xdisp");

    $self->count_food;
        
    $self;            
}

sub info_types { 2 }

sub info {
    my ($self, $x, $y) = @_;
    if ($x >= 0 && $x < $self->{width} && $y >= 0 && $y < $self->{height}) {
        ( $self->{data}[$x][$y]{exists},
          $self->{data}[5*int($x/5)][5*int($y/5)]{food} > 1)
    }
    else {
        map { 0 } @{$self->{keyorder}};
    }
}

sub populate {
    my ($self, $n) = @_;
    for (1..$n) {
        push @{$self->{organisms}}, Organism->new(rand($self->{width}), rand($self->{height}));
    }
}

sub population {
    my ($self) = @_;
    scalar @{$self->{organisms}};
}

sub step {
    my ($self) = @_;

    for (my $i = 0; $i < $self->{width}; $i += 5) {
        for (my $j = 0; $j < $self->{height}; $j += 5) {
            if ($self->{data}[$i][$j]{food}) {
                preserve {
                    my $food = $self->{data}[$i][$j]{food};
                    glTranslate($i+2.5,$j+2.5,0);
                    glColor($food/10_000,$food/10,$food/500);
                    Glop::Draw->Circle(-radius => 2.5);
                };
            }
        }
    }

    for (1..$self->{resource}) {
        my $x = 5*int rand($self->{width}/5);
        my $y = 5*int rand($self->{height}/5);
        next if $x < 5 || $y < 5 || $x >= $self->{width}-6 || $y >= $self->{height}-6;
        my $amt = $self->{data}[$x][$y]{food};
        next if $amt < 1;

        for ([-5,0], [5,0], [0,-5], [0,5]) {
            if ($self->{data}[$x+$_->[0]][$y+$_->[1]]{food} < $self->{cap}) {
                $self->{data}[$x+$_->[0]][$y+$_->[1]]{food} += $amt/10;
                $self->{total_food} += $amt/10;
            }
        }
    }
    
    my $downstep = $self->{stepno}++ % 10 == 0;
    for (my $i = 0; $i < @{$self->{organisms}}; $i++) {
        my $org = $self->{organisms}[$i];
        if ($downstep) {
            $org->{px} += $self->{xdisp};
            $org->{py} += $self->{ydisp};
        }
        my $step = $org->step($self);
        my ($x, $y) = $org->position;
        if (!$step) {
            splice @{$self->{organisms}}, $i, 1;
            $i--;
            next;
        }

        my $penalty = int($self->{stepno} / 5);
        if ($x < 0) { 
            $org->{px} = $self->{width}-1; 
            #$org->{life} -= $penalty;
        }
        if ($x >= $self->{width}) { 
            $org->{px} = 0; 
            #$org->{life} -= $penalty;
        }
        if ($y < 0) { 
            $org->{py} = $self->{height}-1;
            $org->{life} -= $penalty;
        }
        if ($y >= $self->{height}) { 
            $org->{py} = 0;
            $org->{life} -= $penalty;
        }
        
        $org->draw;
    }
}

sub add {
    my ($self, $org) = @_;
    push @{$self->{organisms}}, $org;
}

sub eat {
    my ($self, $x, $y) = @_;
    if ($x >= 0 && $y >= 0 && $x < $self->{width} && $y < $self->{height}) {
        my $nx = 5*int($x/5);
        my $ny = 5*int($y/5);
        if ($self->{data}[$nx][$ny]{food} > 1) {
            $self->{data}[$nx][$ny]{food}--;
            $self->{total_food}--;
            10;
        }
        elsif ($self->{data}[$nx][$ny]{food} > 0) {
            my $ret = $self->{data}[$nx][$ny]{food};
            $self->{data}[$nx][$ny]{food} = 0;
            $self->{total_food} -= $ret;
            10 * $ret;
        }
        else {
            -5;
        }
    }
    else {
        -5;
    }
}

sub count_food {
    my ($self) = @_;
    my $count = 0;
    for (my $i = 0; $i < $self->{width}; $i += 5) {
        for (my $j = 0; $j < $self->{height}; $j += 5) {
            $count += $self->{data}[$i][$j]{food};
        }
    }
    $self->{total_food} = $count;
}

sub total_food {
    my ($self) = @_;
    $self->{total_food};
}

1;
