#!/usr/bin/perl

use strict;
use Chart::Graph qw<gnuplot>;
use IO::Prompt;

sub battle {
	my ($pA, $levA, $pB, $levB) = @_;
	my ($c, $iters) = (0,0);
	while ($c < $levB && $c > -$levA) {
		$c++ if rand() < $pA;
		$c-- if rand() < $pB;
		$iters++;
	}
	($c > 0, $iters)
}

sub battles {
	my ($times, @ps) = @_;
	my ($win, $iters) = (0,0);
	for (1..$times) {
		my ($w, $i) = battle(@ps);
		$win += $w;
		$iters += $i;
	}
	$win /= $times;
	$iters /= $times;
	return ($win, $iters);
}

sub plot {
	my ($title, $xaxis, $yaxis,
		$minx, $maxx, $xsteps,
		$f) = @_;

	my @xs;
	my @ys;
	for (0..$xsteps) {
		my $x = ($maxx - $minx) * $_ / $xsteps + $minx;
		my $y = $f->($x);
		push @xs, $x;
		push @ys, $y;
	}
	
	gnuplot({ title => $title, "x-axis label" => $xaxis, "y-axis label" => $yaxis,
		      "output file" => 'gnuplot.png' },
			[ { type => "columns" }, \@xs, \@ys ]);
	system 'eog gnuplot.png';
}


my %PLOTS = (
	'P vs 1-P to win' => {
		params => [ 'level A', 'level B' ],
		code => sub { 
			my ($levelA, $levelB) = @_;
			plot "P ($levelA) vs 1-P ($levelB)", 'P', 'Probability of winning',
			     0, 1, 100,
				 sub {
					 my ($p) = @_;
					 my ($win, $iters) = battles(1000, $p, $levelA, 1-$p, $levelB);
					 $win;
			     };
		},
	},
	'P vs 1-P battle time' => {
		params => [ 'level A', 'level B' ],
		code => sub { 
			my ($levelA, $levelB) = @_;
			plot "P ($levelA) vs 1-P ($levelB)", 'P', 'Time of battle',
			     0, 1, 100,
				 sub {
					 my ($p) = @_;
					 my ($win, $iters) = battles(1000, $p, $levelA, 1-$p, $levelB);
					 $iters;
			     };
		},
	},
);

my %MENU = map { $_ => $_ } keys %PLOTS;

while (my $ch = prompt -menu => \%MENU) {
	my $h = $PLOTS{$ch};
	my @params;
	for my $param (@{$h->{params}}) {
		push @params, prompt "$param = ";
	}
	$h->{code}->(@params);
}
