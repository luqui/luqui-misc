#!/usr/bin/perl

use strict;
use Data::Dumper;

my @term;
my @op;

sub Shift {
    my ($t) = @_;
    if ($t =~ /[0-9]+/) {
        push @term, $t;
    }
    else {
        push @op, $t;
    }
}

sub Reduce {
    my $t = pop @op;
    if ($t =~ /[@&]/) {
        die "Parse error" if @term < 2;
        push @term, { operator => $t, b => pop @term, a => pop @term };
    }
    elsif ($t =~ /%/) {
        die "Parse error" if @term < 1;
        push @term, { operator => $t, a => pop @term };
    }
}

my %prec = (
    '@' => { qw{ @ -1  %  1 &  1 ( -1 )  1 } },
    '%' => { qw{ @ -1  %  1 &  1 ( -1 )  1 } },
    '&' => { qw{ @ -1  % -1 &  1 ( -1 )  1 } },
    '(' => { qw{ @  1  %  1 &  1 (  1 )  0 } },
    ')' => { qw{ @ -1  % -1 & -1 ( -1 ) -1 } },
);

sub CmpPrec {
    my ($a, $b) = @_;
    $prec{$a}{$b};
}

sub ReduceQ {
    my ($t) = @_;
    my $o = $op[-1];
    if (CmpPrec($t, $o) < 0) {
            return 1;
    }
    else {
            return 0;
    }
}

sub NextToken {
    print "$_[0]\n";
    if ($_[0] =~ s/^([0-9]+|[()@&%\$])//) {
        return $1;
    }
    else {
        die "Lex Error: $_[0]\n";
    }
}

sub Parse {
    my ($str) = @_;
    $str .= '$';
    Shift(NextToken($str));
    my $tok = NextToken($str);
    while (@op || $tok ne '$') {
        print "@term | @op\n";
        if ($tok eq '$') {
            Reduce();
        }
        elsif ($tok =~ /[0-9]+/) {
            Shift($tok);
            $tok = NextToken($str);
        }
        else {
            if (ReduceQ($tok)) {
                Reduce();
            }
            else {
                Shift($tok);
                $tok = NextToken($str);
            }
        }
    }
    return $term[-1];
}

print Dumper(Parse($ARGV[0]));
