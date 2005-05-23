#!/usr/bin/perl

use strict;

use Fcntl;
use Time::HiRes qw<usleep>;
use POE;

my $seed = $ARGV[1] || int rand(1 << 16);
srand $seed;
print "$seed\n";

my %events = (
    'off'   => 0x80,
    'on'    => 0x90,
    'meta'  => 0xb0,
    'patch' => 0xc0,
);

open my $dev, '> /dev/midiplay';  # /dev/snd/midiC0D2
select $dev;
$|=1;
select STDOUT;

sub ev {
    my ($channel, $type, @data) = @_;
    print $dev pack('C*', $events{$type} + $channel || $type, @data);
}

our $BEAT = 2;
our $GREG = 0;
our $STOP = 0;
our $STOPPED = 0;

our $STOP_P = 0.01;

$SIG{INT} = sub { $STOP = 1 };
$SIG{QUIT} = sub { exit };

my @voices = @{do $ARGV[0] or die "Couldn't open $ARGV[0]: $!"};

POE::Session->create(
    inline_states => {
        last_note => sub {
            my ($self, $prev) = @_[ARG0..$#_];
            ev $self->{channel}, on => $prev, 0;
        },
        
        next_note => sub {
            my ($prev, $voice, $self, $register, $stop) = @_[ARG0..$#_];
            
            if ($STOPPED == @voices) {
                $_[KERNEL]->delay_add('last_note', 2, $self, $prev);  # 2 second finish
                return;
            }
            
            ev $self->{channel}, on => $prev, 0;


            if ($STOP || rand >= $STOP_P) {
                unless (@$voice) { 
                    if ($STOP && !$stop) {
                        $STOPPED++;
                        $_[KERNEL]->yield('next_note', 0, $self->{final}, $self, $register, 1) if $self->{final};
                        return;
                    }
                    if ($stop) {
                        if (0.9 > rand) {
                            $voice = [ @{$self->{final}} ];
                        }
                        else {
                            $voice = [ @{$self->{notes}} ];
                        }
                    }
                    else {
                        $voice = [ @{$self->{notes}} ];
                    }
                    if (0.95 < rand && !$stop) {
                        $register = 12*!$register;
                    }
                }
                
                if (0.9 > rand || $stop) {
                    ev $self->{channel}, on => $register + $GREG + $voice->[0], $voice->[1];
                }
                else {
                    ev $self->{channel}, on => $register + $GREG + $voice->[0], 64 + int(rand(64));
                }
                
                $_[KERNEL]->delay_add(
                    'next_note', 
                    $BEAT * $voice->[2], 
                    $voice->[0] + $register + $GREG, 
                    [ @$voice[3..$#$voice] ], 
                    $self, 
                    $register,
                    $stop,
                );
            }
            else {
                $_[KERNEL]->delay_add('next_note', 
                    $BEAT * int(rand(32)) + $BEAT * $voice->[2], 
                    0, 
                    [ @$voice[3..$#$voice] ], 
                    $self, 
                    0,
                    $stop,
                );
            }
        },

        register_change => sub {
            return if $STOP;
            if (0.99 < rand) {
                $_[KERNEL]->yield('register_change_5050');
                $_[KERNEL]->delay_add('register_change_5050', $BEAT * 16);
                $_[KERNEL]->delay_add('register_change', $BEAT * 32);
            }
            else {
                $_[KERNEL]->delay_add('register_change', $BEAT * 4);
            }
        },

        register_change_5050 => sub {
            return if $STOP;
            if (rand > 0.5) {
                $GREG++;
            }
            else {
                $GREG--;
            }
        },

        _start => sub {
            $_[KERNEL]->delay_add('register_change', $BEAT * 16);
            
            for (@voices) {
                ev $_->{channel}, patch => $_->{patch};
                $_[KERNEL]->delay_add('next_note', $BEAT * $_->{enter}, 0, $_->{notes}, $_, 0);
            }
        },
    },
);

POE::Kernel->run;
