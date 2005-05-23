package Music::MWF;

use 5.006001;
use strict;
use warnings;

use MIDI;

sub from_midi {
    my ($self, $file) = @_;
    
    unless (ref $file) {
        $file = MIDI::Opus->new({ from_file => $file }) or return;
    }
    
    my $tracks = $file->tracks_r;
}

sub midi_track_to_mwf_track {
    my ($self, $tick, $track) = @_;
    my @events = @$track;
    my @out;

    my $meter = 4 * $tick;  # ticks per measure (start in 4/4)
    my $measure = 0;
    my $cur = 0;

    push @out, bless { type => 'measure' } => 'Music::MWF::measure';
    
    while (@events) {
        $cur += $events[0];
        if ($cur >= $measure + $meter) {
            push @out, bless { type => 'measure' } => 'Music::MWF::measure';
            $measure += $meter;
        }
    }
}
