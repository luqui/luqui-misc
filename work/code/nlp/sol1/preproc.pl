#!/usr/bin/perl

use FindBin;
use lib $FindBin::Bin;

use Processor::Questioner;
use Processor::DateNormalize;
use Processor::NameAnonymize;
use Processor::PlaceAnonymize;
use Getopt::Long;

my $USAGE = <<EOT;
preproc: Usage: $0 [Options] <file>
    Options:
        -basename -b <name>     Use <name> for the naming scheme
        -root -r <dir>          Put auxiliary files in <dir>
EOT

GetOptions(\my %opt, 
    'basename|b=s',
    'root|r=s',
);

unless (@ARGV == 1) {
    print STDERR $USAGE;
    exit 2;
}

$opt{root} ||= $ARGV[0] =~ /(.*?)\./ ? $1 : 'a';

open my $out, '>', "out/$opt{root}.output.txt" 
    or die "Couldn't open out/$opt{root}.output.txt for writing: $!";

my $questioner = Processor::Questioner->new;

my @processors = (
    Processor::DateNormalize->new("out/$opt{root}.dates.txt", $questioner),
    Processor::NameAnonymize->new("out/$opt{root}.names.txt", $questioner),
    Processor::PlaceAnonymize->new("out/$opt{root}.places.txt", $questioner),
);

my ($lastid, $text);

while (<>) {
    s/(.*?) `// or die "Malformed ID at line $. of $ARGV\n";

    if ($lastid ne $1) {
        if ($text) { 
            print $out "$lastid `$_" for split /^/, process($lastid, $text, $.);
        }
        undef $text;
        $lastid = $1;
    }

    $text .= $_;
}

sub process {
    my ($docid, $text) = @_;
    $text = $_->process($docid, $text) for @processors;
    $text;
}
