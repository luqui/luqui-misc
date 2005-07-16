#!/usr/bin/perl

package Receiver;

use MIDI::Wire;

use base 'MIDI::Wire::Processor';
use base 'MIDI::Wire::DeviceReader';

our @INTERVALS = (
    'octave',
    'min2',
    'maj2',
    'min3',
    'maj3',
    'p4',
    'tritone',
    'p5',
    'min6',
    'maj6',
    'min7',
    'maj7',
);

our $ITICKS = 24;

sub new {
    my ($class, %opts) = @_;
    my $self = bless { 
        ticks => 0,
        keys => { },
        offkeys => { },
        lscore => 0,
        rscore => 0,
        pot    => 0,
    } => ref $class || $class;
    for (@ISA) {
        my $meth = "$_\::init";
        $self->$meth(%opts);
    }
    $self;
}

sub note_on {
    my ($self, %opt) = @_;
    $self->{keys}{$opt{note}} = 1;
    delete $self->{offkeys}{$opt{note}};
}

sub note_off {
    my ($self, %opt) = @_;
    $self->{offkeys}{$opt{note}} = 1;
}

sub raw_timer {
    my ($self) = @_;
    $self->{ticks}++;
    while ($self->{ticks} >= $ITICKS) {
        $self->{ticks} -= $ITICKS;
        $self->register;
    }
}

sub register {
    my ($self) = @_;
    my @keys = sort keys %{$self->{keys}};
    my @left = grep { $_ <= 60 } @keys;
    my @right = grep { $_ > 60 } @keys;
    
    # These lines make holding down keys okay.
    # delete @{$self->{keys}}{keys %{$self->{offkeys}}};
    # $self->{offkeys} = {};
    
    $self->{keys} = {};

    $self->score(\@left, \@right);

    print "\n";
}

sub get_intervals {
    my ($self, @keys) = @_;
    map { @INTERVALS[($_ - $keys[0]) % 12] } @keys[1..$#keys];
}

our %SCORE = (
    octave => 0,
    min2   => 'lose',
    maj2   => -10,
    min3   => 10,
    maj3   => 10,
    p4     => 5,
    tritone => 'lose',
    p5     => 5,
    min6   => 10,
    maj6   => 10,
    min7   => -10,
    maj7   => 'lose',
);
    

sub score {
    my ($self, $left, $right) = @_;

    my @lint = $self->get_intervals(@$left);
    my @rint = $self->get_intervals(@$right);
    my @all  = $self->get_intervals(@$left, @$right);

    my $lplose = 0;
    my $rplose = 0;
    
    for (@lint) {
        if ($SCORE{$_} eq 'lose') {
            $lplose = 1;
        }
    }

    for (@rint) {
        if ($SCORE{$_} eq 'lose') {
            $rplose = 1;
        }
    }

    if ($lplose && $rplose) {
        print "\e[1;31mKILL\e[0m\n";
        $self->{pot} = 0;
    }
    elsif ($lplose) {
        print "\e[1;31mLEFT LOSES\e[0m\n";
        $self->{rscore} += $self->{pot};
        $self->{pot} = 0;
    }
    elsif ($rplose) {
        print "\e[1;31mRIGHT LOSES\e[0m\n";
        $self->{lscore} += $self->{pot};
        $self->{pot} = 0;
    }

    unless ($lplose || $rplose) {
        for (@all) {
            if ($SCORE{$_} eq 'lose') {
                print "\e[1;31mKILL\e[0m\n";
                $self->{pot} = 0;
                $lplose = $rplose = 1;
                last;
            }
        }
    }
    
    unless ($lplose || $rplose) {
        for (@all) {
            print "$_($SCORE{$_}) ";
            $self->{pot} += $SCORE{$_};
        }
        print "\n";
    }

    $self->print_score;
}

sub print_score {
    my ($self) = @_;
    print "\e[1;33m$self->{pot}\e[0m        $self->{lscore} - $self->{rscore}\n";
}

package main;

my $midi = Receiver->new(input => '/dev/midi');
while (1) { $midi->next }
