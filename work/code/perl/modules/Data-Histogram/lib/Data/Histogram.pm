package Data::Histogram;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

use Exporter;
use base 'Exporter';

our @EXPORT = qw<histogram>;

our $VERSION = '0.01';

use overload 
        '""' => \&string,
;

sub histogram {
    my (@data) = @_;
    my $hist = Data::Histogram->new;
    $hist->add(@data);
    $hist;
}

sub new {
    my ($class) = @_;
    bless {
        data => { },
    } => ref $class || $class;
}

sub from_hash {
    my ($class, %data) = @_;
    bless {
        data => \%data,
    } => ref $class || $class;
}

sub add {
    my ($self, @data) = @_;
    $self->{data}{$_}++ for @data;
}

sub lookup {
    my ($self, $item) = @_;
    0+$self->{data}{$item};
}

sub string {
    my ($self, $scrwid) = @_;
    $scrwid ||= 72;
    
    my $maxkey = 0;
    my $maxval = 0;
    for (keys %{$self->{data}}) {
        my $klen = length $self->{data}{$_} + length $_;
        $maxkey = $klen if $klen > $maxkey;
        $maxval = $self->{data}{$_} if $self->{data}{$_} > $maxval;
    }
    
    my $valwid = $scrwid - $maxkey - 5;
    my $donewlines;
    if ($valwid < 30) {
        $donewlines = 1;
        $valwid = $scrwid - 8;            # 8 character indent
    }
    
    my $result = '';
    for my $key (sort keys %{$self->{data}}) {
        $result .= "$key " . (" " x ($maxkey - length $key)) . "($self->{data}{$key}): ";
        $result .= "\n        " if $donewlines;
        $result .= '#' x ($valwid * $self->{data}{$key} / $maxval);
        $result .= "\n";
    }
    $result;    
}

=head1 NAME

Data::Histogram - create simple ASCIIgraphical histograms

=head1 SYNOPSIS

    # print a 72-column histogram
    print histogram(1, 2, 1, 'hi', 'foo', 'foo');

    # specify a different width like so
    print histogram(1, 2, 1)->string(132);

=head1 DESCRIPTION

This module creates a simple ASCII histogram.  The example in the synopsis
would put output like this (given the appropriate screen width):

    1   (2): ########
    2   (1): ####
    hi  (1): ####
    foo (2): ########

=head1 AUTHOR

Luke Palmer

=head1 COPYRIGHT

This module is public domain.
