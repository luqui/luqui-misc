package MIDI::Wire::Processor;

use 5.006001;
use strict;
use warnings;

use Carp;

our %EVENT = (
    0x80 => { name => 'raw_note_on',            args => 2 },
    0x90 => { name => 'raw_note_off',           args => 2 },
    0xa0 => { name => 'raw_key_aftertouch',     args => 2 },
    0xb0 => { name => 'raw_controller',         args => 2 },
    0xc0 => { name => 'raw_patch',              args => 1 },
    0xd0 => { name => 'raw_channel_aftertouch', args => 1 },
    0xe0 => { name => 'raw_pitch_wheel',        args => 2 },
    0xf0 => { name => 'raw_fnib',               args => 0 },
);

sub next {
    my ($self) = @_;
    my $cmd = $self->read_byte;
    my $hinib = $cmd & 0xf0;
    my $meth = $EVENT{$hinib}{name};
    my $args = $EVENT{$hinib}{args};
    my @args = map { $self->read_byte } 1..$args;
    $self->$meth($cmd, @args);
}

sub raw_note_on {
    my ($self, $cmd, $note, $velocity) = @_;
    my $ch = $cmd & 0x0f;
    $self->note_on(
        channel  => $ch,
        note     => $note,
        velocity => $velocity,
    );
}

sub note_on { }

sub raw_note_off {
    my ($self, $cmd, $note, $velocity) = @_;
    my $ch = $cmd & 0x0f;
    $self->note_off(
        channel  => $ch, 
        note     => $note, 
        velocity => $velocity,
    );
}

sub note_off { }

sub raw_key_aftertouch {
    my ($self, $cmd, $note, $pressure) = @_;
    my $ch = $cmd & 0x0f;
    $self->key_aftertouch(
        channel  => $ch, 
        note     => $note, 
        pressure => $pressure,
    );
}

sub key_aftertouch { }

sub raw_controller {
    my ($self, $cmd, $controller, $value) = @_;
    my $ch = $cmd & 0x0f;
    $self->controller(
        channel    => $ch,
        controller => $controller,
        value      => $value,
    );
}

sub controller { }

sub raw_patch {
    my ($self, $cmd, $patch) = @_;
    my $ch = $cmd & 0x0f;
    $self->patch(
        channel => $ch,
        patch   => $patch,
    );
}

sub patch { }

sub raw_channel_aftertouch {
    my ($self, $cmd, $pressure) = @_;
    my $ch = $cmd & 0x0f;
    $self->channel_aftertouch(
        channel  => $ch,
        pressure => $pressure,
    );
}

sub channel_aftertouch { }

sub raw_pitch_wheel {
    my ($self, $cmd, $lsb, $msb) = @_;
    my $ch = $cmd & 0x0f;
    my $value = ($msb << 8) | $lsb;
    $self->pitch_wheel(
        channel => $ch,
        value   => $value,
    );
}

our %FNIB = (
    0xf0 => { name => 'raw_sysex',              args => 0 },
    0xf1 => { name => 'raw_timecode',           args => 1 },
    0xf2 => { name => 'raw_song_ptr',           args => 2 },
    0xf3 => { name => 'raw_song_select',        args => 1 },
    0xf6 => { name => 'raw_tune',               args => 0 },
    0xf7 => { name => 'raw_end_sysex',          args => 0 },
    0xf8 => { name => 'raw_timer',              args => 0 },
    0xfa => { name => 'raw_start',              args => 0 },
    0xfb => { name => 'raw_continue',           args => 0 },
    0xfc => { name => 'raw_stop',               args => 0 },
    0xfe => { name => 'raw_active_sensing',     args => 0 },
    0xff => { name => 'raw_system_reset',       args => 0 },
);

sub raw_fnib {
    my ($self, $cmd) = @_;
    my $meth = $FNIB{$cmd}{meth};
    my $args = $FNIB{$cmd}{args};
    my @args = map { $self->read_byte } 1..$args;
    $self->$meth($cmd, @args);
}

sub raw_sysex          { }
sub raw_timecode       { }
sub raw_song_ptr       { }
sub raw_song_select    { }
sub raw_tune           { }
sub raw_end_sysex      { }
sub raw_timer          { }
sub raw_start          { }
sub raw_continue       { }
sub raw_stop           { }
sub raw_active_sensing { }
sub raw_system_event   { }
