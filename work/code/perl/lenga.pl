#!/usr/bin/perl

use strict;
use Term::ReadLine;
use List::Util qw<max>;

my @STMTS;

my $term = Term::ReadLine->new('Lenga');

sub prove {
	my ($t, @stmts) = @_;
	
	my $list = join '', map { "$_.\n" } @stmts;
	open my $fh, '| otter >& /dev/null';
	print $fh "set(auto).\nassign(max_seconds,$t).\nformula_list(usable).\n";
	print $fh $list;
	print $fh "end_of_list.\n";
	close $fh;
	
	return 1 if $? >> 8 == 103;   # inconsistent (proved)
	return 0 if $? >> 8 == 104;   # consistent (not proved)
	if ($? >> 8 == 106) {
		print "  \e[31mMax search time exceeded.  Assuming consistency.\e[0m\n";
		return 0;
	}
	die "Otter did something naughty ($! ; $?)\n";
}

sub check_consistency {
	unless (prove(15, @STMTS)) {
		print "\e[1;32mTheory consistent.\e[0m\n";
	}
	else {
		print "\e[1;33mTheory inconsistent.\e[0m\n";
	}
}

sub check_independence {
	return if @STMTS <= 1;
	for my $i (reverse 0..$#STMTS) {
		my @stmts = @STMTS;
		$stmts[$i] = "-($stmts[$i])";
		if (prove(max(int(15/@stmts),1), @stmts)) {
			print "\e[1;33mThe axiom '$STMTS[$i]' is a theorem\e[0m\n";
			splice @STMTS, $i, 1;
			return check_independence();
		}
	}
}

while (defined($_ = $term->readline('> '))) {
	my @oldstmts = @STMTS;
	push @STMTS, $_;
	eval {
		check_consistency();
		check_independence();
		1;
	} or do {
		print "\e[1;31mThere was some kind of error ($@).\e[0m\n";
		@STMTS = @oldstmts;
	};
}
