package MIDI::Wire::DeviceReader;

use strict;
use warnings;

use Carp;
use Fcntl qw<O_RDONLY>;

sub init {
    my ($self, %opts) = @_;
    croak "MIDI::Wire::DeviceReader needs an 'input' option"
        unless $opts{input};
    my $fh;
    if (ref $opts{input}) {
        $fh = $opts{input};
    }
    else {
        sysopen $fh, $opts{input}, O_RDONLY
            or croak "Couldn't open $opts{input} for reading: $!";
    }
    $self->{__PACKAGE__ . "/fh"} = $fh;
}

sub read_byte {
    my ($self) = @_;
    my $len = sysread $self->{__PACKAGE__ . "/fh"}, my $out, 1;
    if ($len == 1) {
        return ord $out;
    }
    else {
        return;
    }
}

1;
