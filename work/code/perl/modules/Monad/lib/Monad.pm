package Monad;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

use Filter::Simple;
use Text::Balanced qw<extract_codeblock>;
use PPI;
use PPI::Dumper;

FILTER {
    local %PPI::Token::Operator::OPERATOR = (
        %PPI::Token::Operator::OPERATOR,
        '<-' => 1,
    );
    $_ = filter($_);
    if ($_[1] eq '-debug') {
        print STDERR $_;
    }
    $_;
};

sub filter {
    my ($text) = @_;
    while ($text =~ /DO \s* (?= \{ )/gx) {
        my $prepos = $-[0];
        my ($extracted) = extract_codeblock $text;
        my $postpos = pos $text;

        my $monad = monadize($extracted);
        substr($text, $prepos, $postpos - $prepos) = $monad;
        pos $text = $postpos + length($monad) - length($extracted);
    }
    $text;
}

sub monadize {
    my ($text) = @_;
    $text = filter($text);
    
    my $doc = PPI::Document->new(\$text);
    $doc->prune('PPI::Token::Comment');
    my ($block) = $doc->children;
    my @top = $block->children;
    my $final = 'do{';
    my $tail;

    my $nstmts = grep { $_->isa('PPI::Statement') } @top;
    my $stmtct = 0;

    for (@top) {
        if ($_->isa('PPI::Statement')) {
            my $str = $_;
            $str =~ s/;\s*$//;
            if ($str =~ /^\s*\^/) {
                $str =~ s/\^//;
                $final .= "$str;";
                $stmtct++;
            }
            elsif (++$stmtct == $nstmts) {
                $final .= "$str";
            }
            elsif ($str =~ /<-/) {
                my ($left, $right) = split /<-/, $str;
                $final .= "Monad::BIND(do{$right}, sub { ($left) = \@_; ";
                $tail .= "})";
            }
            else {
                $final .= "Monad::BIND(do{$str}, sub { ";
                $tail .= "})";
            }
        }
        else {
            $final .= $_;
        }
    }
    $final .= "$tail}";
}

sub BIND {
    my ($monad, $function) = @_;
    if (ref $monad eq 'ARRAY') {    # make the list monad pervasive
        Monad::List::BIND($monad, $function);
    }
    else {
        $monad->BIND($function);
    }
}

1;
