package Tie::Hash::Vivify;

use 5.006001;
use strict;
use warnings;

our $VERSION = 0.01;

use Tie::Hash;
use base 'Tie::ExtraHash';

sub new {
    my ($class, $defsub) = @_;
    tie my %hash => $class, $defsub;
    \%hash;
}

sub TIEHASH {
    my ($class, $defsub) = @_;
    bless [{}, $defsub] => ref $class || $class;
}

sub FETCH {
    my ($self, $key) = @_;
    my ($hash, $defsub) = @$self;
    if (exists $hash->{$key}) {
        $hash->{$key};
    }
    else {
        $hash->{$key} = $defsub->();
    }
}

1;


=head1 NAME

Tie::Hash::Vivify - Create hashes that autovivify in interesting ways.

=head1 SYNOPSIS

    use Tie::Hash::Vivify;

    my $default = 0;
    tie my %hash => 'Tie::Hash::Vivify', sub { "default" . $default++ };
    print $hash{foo};   # default0
    print $hash{bar};   # default1
    print $hash{foo};   # default0
    $hash{baz} = "hello";
    print $hash{baz};   # hello

    my $hashref = Tie::Hash::Vivify->new(sub { "default" });
    $hashref->{foo};    # default
    # ...

=head1 DESCRIPTION

This module implements a hash where if you read a key that doesn't exist, it
will call a code reference to fill that slot with a value.

You can either tie to the C<Tie::Hash::Vivify> package:

    tie my %hash => 'Tie::Hash::Vivify', sub { "my default" };

Or you can create a new anonymous reference to a C<Tie::Hash::Vivify> hash:

    my $hashref = Tie::Hash::Vivify->new(sub { "my default" });

=head1 AUTHOR

Luke Palmer, lrpalmer gmail com

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2005 by Luke Palmer

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.8.6 or,
at your option, any later version of Perl 5 you may have available.
