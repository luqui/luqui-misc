#!/usr/bin/perl

use PPI;
use PPI::Dumper;

my $doc;
{
    local %PPI::Token::Operator::OPERATOR = (
        %PPI::Token::Operator::OPERATOR,
        '<-' => 1,
    );
    $doc = PPI::Document->new($0);
}
my $dumper = PPI::Dumper->new($doc);

$foo = sub {
    my ($x, $y) <- (1,2);
    $x + $y
};

$dumper->print;
