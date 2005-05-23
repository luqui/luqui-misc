#!/usr/bin/perl -l

use Data::COW;
use Perl6::Attributes;

my $self = {};

sub try(&) {
    my ($code) = @_;
    my $old = $self;
    $self = make_cow_ref $self;
    eval {
        $code->(); 1;
    } or $self = $old;
}

$.foo = "foo";

print $.foo;

try {
    $.foo = "bar";
};

print $.foo;

try {
    $.foo = "quux";
    die;
};

print $.foo;

$.foo = "outer";
try {
    $.foo = "middle";
    try {
        $.foo = "inner";
    };
};

print $.foo;

$.foo = "outer";
try {
    $.foo = "middle";
    try {
        $.foo = "inner";
        die;
    };
};

print $.foo;
