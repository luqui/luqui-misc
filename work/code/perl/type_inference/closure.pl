#!/usr/bin/perl

use strict;
use warnings;
no warnings 'uninitialized';

use Symbol::Opaque;

BEGIN {
    defsym('type');
    defsym('list');
    defsym('does');
}

my @rules = (
    does( type('a') => list(type('a')) ),
    does( list(list(type('a'))) => type('Num') ),
    does( type('c') => type('a') ),
);

my @queue = @rules;
my @closure = @rules;

sub insert_rule {
    my ($rule) = @_;
    unless (grep { $rule << $_ } @closure) {
        print "    Inserted " . symstr($rule) . "\n";
        push @closure, $rule;
        push @queue, $rule;
    }
}

sub replace {
    my ($type, $pat, $repl) = @_;
    if ($pat << $type) {
        $repl;
    }
    elsif (list(my $t) << $type) {
        list(replace($t, $pat, $repl));
    }
    else {
        undef;
    }
}

sub process {
    no warnings 'void';

    my ($rule) = @_;
    
    # x -> y:    s(y) -> a ==> s(x) -> a
    if (does( type(my $t), my $ruler ) << $rule) {
        for my $subrule (@closure) {
            does( my $subrulel, my $subruler ) << $subrule;
            if (my $repl = replace($subrulel, $ruler, type($t))) {
                insert_rule(does($repl, $subruler));
            }
        }
    }
    
    # x -> y:    a -> s(x) ==> a -> s(y)
    if (does( my $rulel, type(my $t) ) << $rule) {
        for my $subrule (@closure) {
            does( my $subrulel, my $subruler ) << $subrule;
            if (my $repl = replace($subruler, $rulel, type($t))) {
                insert_rule(does($subrulel, $repl));
            }
        }
    }
}

sub symstr {
    my ($sym) = @_;
    if (does(my $lhs, my $rhs) << $sym) {
        "does( " . symstr($lhs) . ", " . symstr($rhs) . " )";
    }
    elsif (type(my $t) << $sym) {
        "type(" . symstr($t) . ")";
    }
    elsif (list(my $t) << $sym) {
        "list(" . symstr($t) . ")";
    }
    else {
        $sym;
    }
}

while (@queue) {
    my $next = shift @queue;
    print "Processing " . symstr($next) . "\n";
    process($next);
}

print "CLOSURE:\n";
for (@closure) {
    print "  " . symstr($_) . "\n";
}
