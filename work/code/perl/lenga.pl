#!/usr/bin/perl

use strict;
use Term::ReadLine;
use IPC::Open2;
use List::Util qw<max>;

my @STMTS;

my $term = Term::ReadLine->new('Lenga');

sub prove {
	my ($t, @stmts) = @_;
	
	my $list = join '', map { " " x 8 . "$_.\n" } @stmts;
	my $pid = open2(my $out, my $in, 'otter 2>/dev/null');
	
	print $in <<PRELUDE;
      set(auto).
      assign(max_seconds,$t).
      formula_list(usable).
	    all x (x = x).
PRELUDE
	print $in $list;
	print $in "end_of_list.\n";
	close $in;

	my $outs = join '', <$out>;
	close $out;
	waitpid($pid, 0);
	
	return 1 if $? >> 8 == 103;   # inconsistent (proved)
	return 0 if $? >> 8 == 104;   # consistent (not proved)
	if ($? >> 8 == 106) {
		print "  \e[31mMax search time exceeded.  Assuming consistency.\e[0m\n";
		return 0;
	}
	die "Otter did something naughty ($! ; $?):\n$outs";
}

sub check_consistency {
	unless (prove(15, @STMTS)) {
		print "\e[1;32mTheory consistent.\e[0m\n";  1;
	}
	else {
		print "\e[1;33mTheory inconsistent.\e[0m\n";  0;
	}
}

sub check_independence {
	my ($stmtnum) = @_;
	return if @STMTS == 0;
	my @stmts = @STMTS;
	$stmts[$stmtnum] = "-($stmts[$stmtnum])";
	if (prove(max(int(15/@stmts),1), @stmts)) {
		print "\e[1;33mThe axiom '$STMTS[$stmtnum]' is a theorem\e[0m\n";
		splice @STMTS, $stmtnum, 1;
		return 0;
	}
	else {
		return 1;
	}
}

sub errcheck(&) {
	my ($code) = @_;
	eval {
		$code->(); 1;
	} or do {
		print "\e[1;31mThere was some kind of error ($@).\e[0m\n";
		return 0;
	};
	return 1;
}

my $AUTOCHECK = 0;

while (defined($_ = $term->readline('> '))) {
	if ($_ =~ /^\s*list\s*$/) {
		print "$_:  $STMTS[$_]\n" for 0..$#STMTS;
		next;
	}
	elsif ($_ =~ /^\s*inconsistent\s*$/) {
		errcheck { check_consistency() };
	}
	elsif ($_ =~ /^\s*theorem (\d+)\s*$/) {
		errcheck { check_independence($1) and print "Nope.\n" };
	}
	elsif ($_ =~ /^\s*kill (\d+)\s*$/) {
		splice @STMTS, $1, 1;
	}
	elsif ($_ =~ /^\s*autocheck\s*$/) {
		$AUTOCHECK = !$AUTOCHECK;
		print "Autocheck " . ($AUTOCHECK ? "on" : "off") . "\n";
	}
	else {
		my @oldstmts = @STMTS;
		push @STMTS, $_;

		if ($AUTOCHECK) {
			errcheck { 
				if (check_consistency()) {
					check_independence();
				}
				else {
					print "I'm going to pretend you didn't say that...\n";
					@STMTS = @oldstmts;
				}
			} or do {
				print "I'm going to pretend you didn't say that...\n";
				@STMTS = @oldstmts;
			};
		}
	}
}
