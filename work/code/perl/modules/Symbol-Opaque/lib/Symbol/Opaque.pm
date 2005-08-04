package Symbol::Opaque;

our $VERSION = '0.01';

use 5.006001;
use strict;
use warnings;
use Carp;
use Scalar::Util qw<blessed readonly>;

use overload '<<'  => sub { $_[0]->_op_unify($_[1]) },
             '""'  => sub { $_[0]->string },
;

use Exporter;
use base 'Exporter';

our @EXPORT = qw<defsym>;

sub defsym {
    my ($name) = @_;
    my $package = caller;
    no strict 'refs';
    my $code = sub { Symbol::Opaque->new($name, \(@_)) };
    *{"$package\::$name"} = $code;
    $code;
}

sub new {
    my ($class, $name, @refs) = @_;
    bless {
        name => $name,
        refs => \@refs,
    } => ref $class || $class;
}

sub _op_unify {
    my ($self, $other) = @_;
    ! !$self->unify($other);
}

sub name {
    my ($self) = @_;
    $self->{name};
}

sub args {
    my ($self) = @_;
    map { $$_ } @{$self->{refs}};
}

sub subunify {
    my ($self, $leftref, $right) = @_;
    if (!defined $$leftref && !readonly $$leftref) {  # a free variable
        $$leftref = $right;
        return sub { undef $$leftref };
    }
    elsif (blessed($$leftref) && $$leftref->isa('Symbol::Opaque')) {
        return $$leftref->unify($right);
    }
    else {
        return $$leftref eq $right ? sub { } : 0;
    }
}

sub unify {
    my ($self, $other) = @_;
    unless (blessed($other) && $other->isa('Symbol::Opaque')) {
        return 0;
    }
    
    my @oargs = $other->args;
    if (@{$self->{refs}} != @oargs) {
        return 0;
    }
    
    my @rollback;
    for my $i (0..$#oargs) {
        my $unif = $self->subunify($self->{refs}[$i], $oargs[$i]);
        if ($unif) {
            push @rollback, $unif;
        }
        else {
            $_->() for @rollback;
            return 0;
        }
    }
    
    return sub { $_->() for @rollback };
}

sub string {
    my ($self) = @_;
    "$self->{name}(" . join(', ', $self->args) . ")";
}

1;

=head1 NAME

Symbol::Opaque - ML-ish data constructor pattern matching

=head1 SYNOPSIS

    use Symbol::Opaque;

    BEGIN { 
        defsym('foo');   # define the constructor "foo"
        defsym('bar');   # define the constructor "bar"
    }

    if ( foo(my $x) << foo(4) ) {    # bind foo(4) into foo($x)
        # $x is now 4
    }
    
    if ( foo(13, bar(my $x)) << foo(13, bar("baz")) ) {
        # $x is now "baz"
    }

    if ( foo(my $x) << bar(42) ) {
        # not executed: foo(X) doesn't match bar(42)
    }

=head1 DESCRIPTION

This module allows the creation of data constructors, which can then be
conditionally unified like in Haskell or ML.  When you use the B<binding>
operator C<<< << >>>, between two structures, this module tries to bind any
I<free variables> on the left in order to make the structures the same. 
For example:

    foo(my $x) << foo(14)           # true, $x becomes 14

This will make $x equal 14, and then the operator will return true.  Sometimes
it is impossible to make them the same, and in that case no variables are
changed and the operator returns false.  For instance:

    foo(my $x, 10) << foo(20, 21)   # impossible: false, $x is undef

This makes it possible to write cascades of tests on a value:

    my $y = foo(20, 21);
    if (foo("hello", my $x) << $y) {
        ...
    }
    elsif (foo(my $x, 21) << $y) {
        # this gets executed: $x is 20
    }
    else {
        die "No match";
    }

(Yes, Perl lets you declare the same variable twice in the same cascade -- just
not in the same condition).

Before you can do this, though, you have to tell Perl that C<foo> is such a
data constructor.  This is done with the exported C<defsym> routine.  It is
advisable that you do this in a C<BEGIN> block, so that the execution path
doesn't have to reach it for it to be defined:

    BEGIN {
        defsym('foo');   # foo() is a data constructor
    }

If two different modules both declare a 'foo' symbol, I<they are considered the
same>.  The reason this isn't dangerous is because the only thing that can ever
differ about two symbols is their name: there is no "implementation" defined.

The unification performed is I<unidirectional>: you can only have free
variables on the left side.

The unification performed is I<nonlinear>: you can mention the same free
variable more than once:

    my $x;   # we must declare first when there is more than one mention
    foo($x, $x) << foo(4, 4);  # true; $x = 4
    foo($x, $x) << foo(4, 5);  # false

Unification of arrays and hashes is only performed I<referentially>.  So:

    foo([1,2,3]) << foo([1,2,3]);  # FALSE!

But:

    my $array = [1,2,3];
    foo($array) << foo($array);    # true

It is possible implement this if somebody wants it.

=head1 SEE ALSO

L<Logic>

=head1 AUTHOR

Luke Palmer <lrpalmer at gmail dot com>
