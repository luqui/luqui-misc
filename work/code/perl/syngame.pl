#!/usr/bin/perl

use strict;
use WordNet::QueryData;
use Set::Scalar;
use Term::ReadLine;

print "Initializing...\n";
my $wn = WordNet::QueryData->new;
print "Done.\n";

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

sub multisyn {
	my ($word, $dist) = @_;
	
	my @syn = (Set::Scalar->new($word));
	my $last = $syn[-1];
	while ($dist --> 0) {
		my $set = Set::Scalar->new;
		$set += $_ for map { synset($_) } $last->elements;
		$set -= $_ for @syn;
		last if $set->is_empty;
		push @syn, $set;
		$last = $set;
	}

	@syn;
}

sub ask {
	my ($prompt) = @_;
	my $result = do {
		if ($prompt) {
			$term->readline($prompt);
		}
		else {
			$term->readline('> ');
		}
	};
	exit unless defined $result;
	$result;
}

sub connect_in {
	my ($db, $word) = @_;
	my %seen;
	my @q = map { [$db, $_] } keys %$db;
	while (@q) {
		my ($de, $elem) = @{shift @q};
		next if $seen{$elem}++;
		return if $elem eq $word 
			   or (exists $de->{$elem} && exists $de->{$elem}{$word});
		my $syns = synset($elem);
		if ($syns->has($word)) {
			$de->{$elem}{$word} = {};
			return $elem;
		}

		push @q, map { [$de->{$elem}, $_] } keys %{$de->{$elem}};
	}
	return;
}

sub showdb {
	my ($db, $indent) = @_;
	my $nfirst;
	for (sort keys %$db) {
		print "\n" if $nfirst;
		print +($nfirst ? $indent : "") . $_ . " -> ";
		showdb($db->{$_}, " " x (length($indent) + length($_) + 4));
		$nfirst++;
	}
}

my $DIFFICULTY = 3;

my @words = $wn->listAllWords;

GAME: while (1) {
	my $word = $words[rand @words];
	my @syns = multisyn($word, $DIFFICULTY);
	next unless @syns == $DIFFICULTY+1;
	my @targets = $syns[-1]->elements;
	my $target = $targets[rand @targets];

	print "\n------------------------\n\n";
	print "Connect $word to $target\n\n";
	my %data = ( $word => {} );

	print "Synonyms of $word: " . (synset($word) - $word) . "\n\n";
	
	while ($_ = do { showdb(\%data); print "\n"; ask }) {
		s/ /_/g;

		if (s/^\?\s*//) {
			system "dict '$_'";
			next;
		}

		if (/^_*(.*?)_*\*_*(.*?)_*$/) {
			print "Shared synonyms of $1 and $2: " . (synset($1) * synset($2)) . "\n\n";
			next;
		}
		
		print "Synonyms of $_: " . (synset($_) - $_) . "\n\n";
		my $c = connect_in(\%data, $_);
		print "$_ is a synonym of $c\n" if $c;
		if ($c && $_ eq $target) {
			showdb(\%data);
			print "\n";
			%data = ();
			print "You win!\n";
			next GAME;
		}
	}
}
