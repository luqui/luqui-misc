package Music::MWF::ParseMIDI;

use strict;
use warnings;

use MIDI;
use Perl6::Attributes;

sub new {
    my ($class, $ticks_per_beat, $events) = @_;

    bless {
        events         => $events,
        ticks_per_beat => $tick,

        state => {
            measure => 0,
            cur     => 0,
            meter   => $ticks_per_beat * 4,  # ticks per measure, start in 4/4

            notes   => { },
        },

        output => [ ],
    } => ref $class || $class;
}

sub parse_event {
    my ($self, $event) = @_;
    
    $.state{cur} += $event->[1];   # add delta time
    while ($.state{cur} >= $.state{measure} + $.state{meter}) {
        $.state{measure} += $.state{meter};
        push @.output, Music::MWF::Event::Measure->new;
    }

    my $meth = "parse_event_$event->[0]";
    if ($self->can($meth)) {
       $self->$meth($event);
    } 
}

sub parse_event_note_on {
    my ($self, $event) = @_;
    my (undef, undef, $channel, $note, $velocity) = @$event;
    
    if ($velocity == 0) {
        return $self->parse_event_note_off($event);
    }
    
    if ($.state{notes}{$channel}{$note}) {
        $self->parse_event_note_off(['note_off', $channel, $note, 0]);
    }

    my $event = Music::MWF::Event::Note->new(
        $.state{cur} - $.state{measure}, $channel, $note, $velocity);
    $.state{notes}{$channel}{$note} = {
        start => $.state{cur},
        event => $event,
    };

    push @.output, $event;
}

sub parse_event_note_off {
    my ($self, $event) = @_;
    my (undef, undef, $channel, $note) = @$event;

    my $noteobj = $.state{notes}{$channel}{$note};
    my $dur = $noteobj->{start} - $.state{cur};
    $noteobj->{event}->set_duration($dur);
    delete $.state{notes}{$channel}{$note};
}

sub parse_event_key_after_touch {
    my ($self, $event) = @_;
    my (undef, undef, $channel, $note, $velocity) = @$event;

    push @.output, Music::MWF::Event::KeyAfterTouch->new(
        $.state{cur} - $.state{measure}, $channel, $note, $velocity);
}

# XXX Think about how we do controllers more
sub parse_event_control_change {
    my ($self, $event) = @_;
    my (undef, undef, $channel, $controller, $value) = @_;

    push @.output, Music::MWF::Event::Controller->new(
        $.state{cur} - $.state{measure}, $channel, $controller, $value);
}


