package MIDI::Score::Named;
use 5.6.1;

use strict;
use warnings;

our %NAME_TO_INDEX = (
    note => {
        type => 0,
        starttime => 1,
        duration => 2,
        channel => 3,
        note => 4,
        velocity => 5,
    },
    key_after_touch => {
        type => 0,
        starttime => 1,
        channel => 2,
        note => 3,
        velocity => 4,
    },
    control_change => {
        type => 0,
        starttime => 1,
        channel => 2,
    },
    patch_change => {
        type => 0,
        starttime => 1,
        channel => 2,
        patch => 3,
    },
    channel_after_touch => {
        type => 0,
        starttime => 1,
        channel => 2,
        velocity => 3,
    },
    pitch_wheel_change => {
        type => 0,
        starttime => 1,
        channel => 2,
        pitch_wheel => 3,
    },
    set_sequence_number => {
        type => 0,
        starttime => 1,
        sequence => 2,
    },
    text_event => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    copyright_text_event => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    track_name => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    instrument_name => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    lyric => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    marker => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    cue_point => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_08 => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_09 => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_0a => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_0b => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_0c => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_0d => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_0e => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    text_event_0f => {
        type => 0,
        starttime => 1,
        text => 2,
    },
    end_track => {
        type => 0,
        starttime => 1,
    },
    set_tempo => {
        type => 0,
        starttime => 1,
        tempo => 2,
    },
    smpte_offset => {
        type => 0,
        starttime => 1,
        hr => 2,
        mn => 3,
        se => 4,
        fr => 5,
        ff => 6,
    },
    time_signature => {
        type => 0,
        starttime => 1,
        nn => 2,
        dd => 3,
        cc => 4,
        bb => 5,
    },
    key_signature => {
        type => 0,
        starttime => 1,
        sf => 2,
        mi => 3,
    },
    sequencer_specific => {
        type => 0,
        starttime => 1,
        raw => 2,
    },
    raw_meta_event => {
        type => 0,
        starttime => 1,
        command => 2,
    },
    sysex_f0 => {
        type => 0,
        starttime => 1,
        raw => 2,
    },
    sysex_f7 => {
        type => 0,
        starttime => 1,
        raw => 2,
    },
    song_position => {
        type => 0,
        starttime => 1,
    },
    song_select => {
        type => 0,
        starttime => 1,
        song_number => 2,
    },
    tune_request => {
        type => 0,
        starttime => 1,
    },
    raw_data => {
        type => 0,
        starttime => 1,
        raw => 2,
    },
);

1;
