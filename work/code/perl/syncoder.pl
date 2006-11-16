#!/usr/bin/perl

use strict;
use WordNet::QueryData;
use Set::Scalar;
use Term::ReadLine;

print STDERR "Initializing...\n";
my $wn = WordNet::QueryData->new;
print STDERR "Done.\n";

my $term = Term::ReadLine->new;

sub synset {
	my ($word) = @_;
	
	my @pos = $wn->querySense(lc $word);
	my @sense = map { $wn->querySense($_) } @pos;

	my @words = map { $wn->querySense($_, "syns") } @sense;

	for (@words) {
		s/#.*//;
	}
	
	Set::Scalar->new(map { lc } @words); 
}

while (<>) {
    my @words = split /([^a-zA-Z']+|'s\s+)/;
    for my $word (@words) {
        if ($word =~ /^[a-zA-Z]+$/) {
            my @syns = (synset($word) + Set::Scalar->new($word))->elements;
            @syns = grep { !/_/ } @syns;
            print $syns[rand @syns];
        }
        else {
            print $word;
        }
    }
}
