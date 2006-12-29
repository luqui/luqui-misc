#!/usr/bin/perl

use Data::Dumper;

sub assert($) {
	my ($cond) = @_;
	die "Assertion failed" unless $cond;
	$cond;
}

sub runsim {
	my %params = @_;
	open my $fh, "-|", './main', 
		@params{qw{prob lefton leftoff leftphase righton rightoff rightphase time}};

	my %result;
	assert(<$fh> =~ /Left light/);
	assert(<$fh> =~ /Passes: (\S+)/);
		$result{left_passes} = $1;
	assert(<$fh> =~ /Cycles: (\S+)/);
		$result{left_cycles} = $1;
	assert(<$fh> =~ m#Cars/cycle: (\S+)#);
		$result{left_cpc} = $1;
	assert(<$fh> =~ m#Cars/s:     (\S+)#);
		$result{left_cps} = $1;
	assert(<$fh> =~ /Right light/);
	assert(<$fh> =~ /Passes: (\S+)/);
		$result{right_passes} = $1;
	assert(<$fh> =~ /Cycles: (\S+)/);
		$result{right_cycles} = $1;
	assert(<$fh> =~ m#Cars/cycle: (\S+)#);
		$result{right_cpc} = $1;
	assert(<$fh> =~ m#Cars/s:     (\S+)#);
		$result{right_cps} = $1;
	assert(<$fh> =~ /Cars completing their trip: (\S+)/);
		$result{total_cars} = $1;
	assert(<$fh> =~ /Average time per car: (\S+)s/);
		$result{time_per_car} = $1;
	assert(<$fh> =~ /Slowdown per car: (\S+)s/);
		$result{slowdown} = $1;
	\%result;
}

sub write_data {
	my ($file, $data) = @_;
	open my $fh, '>', $file or die "Couldn't open file: $!";
	print $file join("\n", @$data);
}

sub measure_right_slowdown {
	my @slowdown;
	my @cps;
	my @cpc;
	for (my $i = 1; $i < 20; $i++) {
		my $ans = runsim(
			prob => 1,
			lefton => 1,
			leftoff => 0,
			leftphase => 0,
			righton => $i,
			rightoff => $i,
			rightphase => 0,
			time => 150,
		);
		push @slowdown, $ans->{slowdown};
		push @cps, $ans->{right_cps};
		push @cpc, $ans->{right_cpc};
	}
	write_data('data/right_slowdown', \@slowdown);
	write_data('data/right_cps', \@cps);
	write_data('data/right_cpc', \@cpc);
}

measure_right_slowdown();
