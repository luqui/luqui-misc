package Processor::DateNormalize;

use strict;

use Carp;

our $TWO_THOUSAND_THRESHOLD = 10;  # Won't be referencing any dates past 2010

our %MONTHS = (
    january   => 1,
    february  => 2,
    march     => 3,
    april     => 4,
    may       => 5,
    june      => 6,
    july      => 7,
    august    => 8,
    september => 9,
    october   => 10,
    november  => 11,
    december  => 12,
);

sub _normalize_year {
    my ($self, $year) = @_;
    if (length $year == 2) {
        $year < $TWO_THOUSAND_THRESHOLD ? 2000 + $year : 1900 + $year;
    }
    else {
        $year;
    }
}

sub _make_date {
    my ($self, $id, $orig, $y, $m, $d) = @_;
    if ($m > 12 || $d > 31) {  # probably not actually a date
        return $orig;
    }

    $orig =~ s/\s+/ /g;        # compress spaces
    
    my $date = sprintf '%04d-%02d-%02d', $self->_normalize_year($y), $m, $d;
    print { $self->{log} } "$id `$date\t$orig\n";
    return $date;
}

sub _complain {
    my ($self, $id, $text) = @_;
    carp "Interpretation of '$text' is ambiguous (docid $id)";
    print { $self->{log} } "$id `ERROR: Interpretation of '$text' is ambiguous -- leaving alone\n";
    $text;
}

sub new {
    my ($self, $logfile, $questioner) = @_;
    my $fh;
    unless (ref $logfile) {
        open $fh, '>', $logfile or croak "Couldn't open $logfile for writing: $!";
    }
    else {
        $fh = $logfile;
    }

    bless { 
        ask => $questioner,
        log => $fh,
    } => ref $self || $self;
}

sub process {
    my ($self, $docid, $text) = @_;

    # Simple substitutions should do for now
    local $_ = $text;
    
    s{\b (\d?\d) / (\d?\d) / (\d\d (?:\d\d)?) \b}
     {$self->_make_date($docid, $&, $3, $1, $2)}gex;

    s{\b (\d?\d) / (\d\d (?:\d\d)?) \b}
     {$self->_make_date($docid, $&, $2, $1, 0)}gex;

    my $month = join '|', keys %MONTHS;
    s[\b ($month) \s+ (\d\d?) ,? \s+ (\d\d (?:\d\d)?) \b]
     [ $self->_make_date($docid, $&, $3, $MONTHS{lc $1}, $2) ]gexi;
     
    s[\b ($month) ,? \s+ (\d\d (?:\d\d)?) \b]
     [ $2 <= 31
          ? $self->_complain($docid, $&)  # eg. September 13 -- bail on these cases
          : $self->_make_date($docid, $&, $2, $MONTHS{lc $1}, 0) ]gexi;
    
    $_;
}

1;
