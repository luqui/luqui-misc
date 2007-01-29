#!/usr/bin/perl

use IO::All;

my %ans;

for my $file (io('data/')->all) {
    my $survey = do $file;
    if (exists $survey->{'con-divide'} && exists $survey->{'con-divide'}{'characterization'}) {
        $survey->{'con-divide_explain'} = $survey->{'con-divide'}{'characterization'};
        delete $survey->{'con-divide'}{'characterization'};
    }
    for (keys %$survey) {
        next if /SEED|studentid|fullname/;
        unless (/explain/) {
            my $answer = $survey->{$_};
            if (ref $answer) {
                $answer = join ' ', map { "$_($answer->{$_})" } sort keys %$answer;
            }
            $ans{$_}{$answer}{count}++;
            if ($survey->{"$_\_explain"}) {
                push @{$ans{$_}{$answer}{explain}}, $survey->{"$_\_explain"};
            }
        }
    }
}

for my $question (sort keys %ans) {
    print "$question:\n";
    for my $answer (sort { $ans{$question}{$b}{count} <=> $ans{$question}{$a}{count} 
                               ||  $a cmp $b} keys %{$ans{$question}}) {
        print "  $ans{$question}{$answer}{count} - $answer\n";
        for my $explain (@{$ans{$question}{$answer}{explain}}) {
            print "    $explain\n";
        }
    }
}
