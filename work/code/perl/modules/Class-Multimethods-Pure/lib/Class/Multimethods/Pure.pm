package Class::Multimethods::Pure;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

use Carp;

our %MULTI;
our %MULTIPARAM;

sub _internal_multi {
    my $name = shift or return;
    
    if (@_) {
        my @params;
        until (!@_ || ref $_[0] eq 'CODE') {
            if ($_[0] =~ /^-/) {
                my ($k, $v) = splice @_, 0, 2;
                $k =~ s/^-//;
                $MULTIPARAM{$k} = $v;
            }
            else {
                my $type = shift;
                unless (ref $type) {
                    if (Class::Multimethods::Pure::Type::Unblessed->is_unblessed($type)) {
                        $type = Class::Multimethods::Pure::Type::Unblessed->new($type);
                    }
                    else {
                        $type = Class::Multimethods::Pure::Type::Package->new($type);
                    }
                }
                push @params, $type;
            }
        }
        
        return () unless @_;
        
        my $code = shift;

        my $multi = $MULTI{$name} ||= 
                Class::Multimethods::Pure::Method->new(
                    Variant => $MULTIPARAM{$name}{Variant},
                );
        
        $multi->add_variant(\@params, $code);
    }

    my $pkg = caller 1;
    {
        no strict 'refs';
        no warnings 'redefine';
        *{"$pkg\::$name"} = make_wrapper($name);
    }
    
    @_;
}

sub make_wrapper {
    my ($name) = @_;
    sub {
        my $call = $MULTI{$name}->can('call');
        unshift @_, $MULTI{$name};
        goto &$call;
    };
}

sub multi {
    if (_internal_multi(@_)) {
        croak "Usage: multi name => (Arg1, Arg2, ...) => sub { code };";
    }
}

our @exports = qw<multi all any none subtype Any>;

sub import {
    my $class = shift;
    my $cmd   = shift;
    
    my $pkg = caller;

    if ($cmd eq 'multi') {
        while (@_ = _internal_multi(@_)) { }
    }
    elsif ($cmd eq 'import') {
        for my $export (@_) {
            unless (grep { $_ eq $export } @exports) {
                croak "$export is not exported from " . __PACKAGE__;
            }
            
            no strict 'refs';
            *{"$pkg\::$export"} = \&{__PACKAGE__ . "::$export"};
        }
    }
    elsif (!defined $cmd) {
        for my $export (@exports) {
            no strict 'refs';
            *{"$pkg\::$export"} = \&{__PACKAGE__ . "::$export"};
        }
    }
    else {
        croak "Unknown command: $cmd";
    }
}

sub all(@) {
    Class::Multimethods::Pure::Type::Conjunction->new(
        Class::Multimethods::Pure::Type->promote(@_)
    );
}

sub any(@) {
    Class::Multimethods::Pure::Type::Disjunction->new(
        Class::Multimethods::Pure::Type->promote(@_)
    );
}

sub none(@) {
    Class::Multimethods::Pure::Type::Injunction->new(
        Class::Multimethods::Pure::Type->promote(@_)
    );
}

sub Any() {
    Class::Multimethods::Pure::Type::Any->new;
}

sub subtype($$) {
    Class::Multimethods::Pure::Type::Subtype->new(
        Class::Multimethods::Pure::Type->promote($_[0]), $_[1]
    );
}

package Class::Multimethods::Pure::Type;

use Carp;
use Scalar::Util qw<blessed>;

our $PROMOTE = Class::Multimethods::Pure::Method->new;

sub promote {
    my ($class, @types) = @_;
    map { $PROMOTE->call($_) } @types;
}

{
    my $pkg = sub { "Class::Multimethods::Pure::Type::$_[0]"->new(@_[1..$#_]) };
    $PROMOTE->add_variant(
        [ $pkg->('Subtype', $pkg->('Any'), sub { blessed $_[0] }) ] => sub {
            $_[0];
    });
    
    $PROMOTE->add_variant(
        [ $pkg->('Subtype', $pkg->('Any'), 
            sub { Class::Multimethods::Pure::Type::Unblessed->is_unblessed($_[0]) }) ]
        => sub { 
            Class::Multimethods::Pure::Type::Unblessed->new($_[0])
    });

    $PROMOTE->add_variant(
        [ $pkg->('Any') ] => sub {
            Class::Multimethods::Pure::Type::Package->new($_[0])
    });
}

our $SUBSET = Class::Multimethods::Pure::Method->new;

sub subset {
    my ($self, $other) = @_;
    $SUBSET->call($self, $other);
}

our $EQUAL = Class::Multimethods::Pure::Method->new;

sub equal {
    my ($self, $other) = @_;
    $EQUAL->call($self, $other);
}

sub matches;
sub string;

{   
    my $pkg = sub { Class::Multimethods::Pure::Type::Package->new(
                            'Class::Multimethods::Pure::' . $_[0]) };

    $SUBSET->add_variant(
        [ $pkg->('Type'), $pkg->('Type') ] => sub {
             my ($a, $b) = @_;
             $a == $b;
    });
    
    # If you change this, remember to change Type::Package::subset
    # which is used in the bootstrap.
    $SUBSET->add_variant( 
        [ $pkg->('Type::Package'), $pkg->('Type::Package') ] => sub {
             my ($a, $b) = @_;
             $a->name->isa($b->name);
     });
    
    $SUBSET->add_variant(
        [ $pkg->('Type::Unblessed'), $pkg->('Type::Unblessed') ] => sub {
             my ($a, $b) = @_;
             $a->name eq $b->name;
    });

    $SUBSET->add_variant(
        [ $pkg->('Type::Any'), $pkg->('Type::Normal') ] => sub { 0 });

    $SUBSET->add_variant(
        [ $pkg->('Type::Normal'), $pkg->('Type::Any') ] => sub { 1 });

    $SUBSET->add_variant(
        [ $pkg->('Type::Any'), $pkg->('Type::Any') ] => sub { 1 });

    $SUBSET->add_variant(
        [ $pkg->('Type::Subtype'), $pkg->('Type::Subtypable') ] => sub {
            my ($a, $b) = @_;
            $a->base->subset($b);
        });

    $SUBSET->add_variant(
        [ $pkg->('Type::Subtypable'), $pkg->('Type::Subtype') ] => sub { 0 });

    our $indent = 0;
    $SUBSET->add_variant(
        [ $pkg->('Type::Subtype'), $pkg->('Type::Subtype') ] => sub {
            my ($a, $b) = @_;
            $a->equal($b) || $a->base->subset($b);
        });
    
    $SUBSET->add_variant(
        [ $pkg->('Type::Junction'), $pkg->('Type') ] => sub {
             my ($a, $b) = @_;
             $a->logic(map { $_->subset($b) } $a->values);
    });

    $SUBSET->add_variant(
        [ $pkg->('Type'), $pkg->('Type::Junction') ] => sub {
             my ($a, $b) = @_;
             $b->logic(map { $a->subset($_) } $b->values);
    });

    $SUBSET->add_variant(
        [ $pkg->('Type::Junction'), $pkg->('Type::Junction') ] => sub {
             my ($a, $b) = @_;
             # just like (Junction, Type)
             $a->logic(map { $_->subset($b) } $a->values);
     });

    #############
     
    $EQUAL->add_variant(
        [ $pkg->('Type'), $pkg->('Type') ] => sub {
            0;
    });

    # If you change this, you should also change the bootstrap, Type::Package::equal.
    $EQUAL->add_variant(
        [ $pkg->('Type::Package'), $pkg->('Type::Package') ] => sub {
            my ($a, $b) = @_;
            $a->name eq $b->name;
    });

    $EQUAL->add_variant(
        [ $pkg->('Type::Unblessed'), $pkg->('Type::Unblessed') ] => sub {
            my ($a, $b) = @_;
            $a->name eq $b->name;
    });

    $EQUAL->add_variant(
        [ $pkg->('Type::Any'), $pkg->('Type::Any') ] => sub { 1 });

    $EQUAL->add_variant(
        [ $pkg->('Type::Subtype'), $pkg->('Type::Subtype') ] => sub {
            my ($a, $b) = @_;
            $a->base == $b->base && $a->condition == $b->condition;
    });

    my $jequal = sub {
        my ($a, $b) = @_;
        !$a->logic(map { !$_->subset($b) } $a->values)
        && $a->logic(map { $b->subset($_) } $a->values);
    };

    
    $EQUAL->add_variant(
        [ $pkg->('Type::Junction'), $pkg->('Type') ] => sub {
            $jequal->($_[0], $_[1]);
    });

    $EQUAL->add_variant(
        [ $pkg->('Type'), $pkg->('Type::Junction') ] => sub {
            $jequal->($_[1], $_[0]);
    });

    $EQUAL->add_variant(
        [ $pkg->('Type::Junction'), $pkg->('Type::Junction') ] => sub {
            $jequal->($_[0], $_[1]);
    });
}


package Class::Multimethods::Pure::Type::Package;

# A regular package type
use base 'Class::Multimethods::Pure::Type';

use Scalar::Util qw<blessed>;

sub new {
    my ($class, $package) = @_;
    bless {
        name => $package,
    } => ref $class || $class;
}

# This is overridden for bootstrapping purposes.  If you change
# logic here, you should change it in the multimethod above
# too.
sub subset {
    my ($self, $other) = @_;
    
    if (ref $self eq __PACKAGE__ && ref $other eq __PACKAGE__) {
        $self->name->isa($other->name);
    }
    else {
        $self->SUPER::subset($other);
    }
}

# Again, bootstrapping.
sub equal {
    my ($self, $other) = @_;

    if (ref $self eq __PACKAGE__ && ref $other eq __PACKAGE__) {
        $self->name eq $other->name;
    }
    else {
        $self->SUPER::equal($other);
    }
}

sub name {
    my ($self) = @_;
    $self->{name};
}

sub matches {
    my ($self, $obj) = @_;
    blessed($obj) ? $obj->isa($self->name) : 0;
}

sub string {
    my ($self) = @_;
    $self->name;
}

package Class::Multimethods::Pure::Type::Normal;

# Non-junctive thingies
use base 'Class::Multimethods::Pure::Type';

package Class::Multimethods::Pure::Type::Subtypable;

use base 'Class::Multimethods::Pure::Type::Normal';

package Class::Multimethods::Pure::Type::Unblessed;

# SCALAR, ARRAY, etc.
use base 'Class::Multimethods::Pure::Type::Subtypable';
use Carp;

our %SPECIAL = (
    SCALAR => 1,
    ARRAY  => 1,
    HASH   => 1,
    CODE   => 1,
    REF    => 1,
    GLOB   => 1,
    LVALUE => 1,
);

sub is_unblessed {
    my ($class, $name) = @_;
    $SPECIAL{$name};
}

sub new {
    my ($class, $name) = @_;
    croak "$name is not a valid unblessed type" 
        unless $SPECIAL{$name};
    bless {
        name => $name,
    } => ref $class || $class;
}

sub name {
    my ($self) = @_;
    $self->{name};
}

sub matches {
    my ($self, $obj) = @_;
    $self->name eq ref $obj;
}

sub string {
    my ($self) = @_;
    $self->name;
}

package Class::Multimethods::Pure::Type::Any;

# Anything whatever

use base 'Class::Multimethods::Pure::Type::Normal';

sub new {
    my ($class) = @_;
    bless { } => ref $class || $class;
}

sub matches {
    my ($self, $obj) = @_;
    1;
}

sub string {
    my ($self) = @_;
    "Any";
}

package Class::Multimethods::Pure::Type::Subtype;

# A restricted type

use base 'Class::Multimethods::Pure::Type::Subtypable';

sub new {
    my ($class, $base, $condition) = @_;
    bless {
        base => $base,
        condition => $condition,
    } => ref $class || $class;
}

sub base {
    my ($self) = @_;
    $self->{base};
}

sub condition {
    my ($self) = @_;
    $self->{condition};
}

sub matches {
    my ($self, $obj) = @_;
    $self->base->matches($obj) && $self->condition->($obj);
}

sub string {
    my ($self) = @_;
    "where(" . $self->base->string . ", {@{[$self->condition]}})";
}

package Class::Multimethods::Pure::Type::Junction;

# Any junction type

use base 'Class::Multimethods::Pure::Type';

sub new {
    my ($class, @types) = @_;
    bless {
        values => \@types,
    } => ref $class || $class;
}

sub values {
    my ($self) = @_;
    @{$self->{values}};
}

sub matches {
    my ($self, $obj) = @_;
    $self->logic(map { $_->matches($obj) } $self->values);
}

sub logic;  # takes a list of true/false values and returns
            # the boolean evaluation of them

package Class::Multimethods::Pure::Type::Disjunction;

# An any type
use base 'Class::Multimethods::Pure::Type::Junction';

sub logic {
    my ($self, @values) = @_;
    for (@values) {
        return 1 if $_;
    }
    return 0;
}

sub string {
    my ($self) = @_;
    'any(' . join(', ', map { $_->string } $self->values) . ')';
}

package Class::Multimethods::Pure::Type::Conjunction;

# An all type
use base 'Class::Multimethods::Pure::Type::Junction';

sub logic {
    my ($self, @values) = @_;
    for (@values) {
        return 0 unless $_;
    }
    return 1;
}

sub string {
    my ($self) = @_;
    'all(' . join(', ', map { $_->string } $self->values) . ')';
}

package Class::Multimethods::Pure::Type::Injunction;

# A none type
use base 'Class::Multimethods::Pure::Type::Junction';

sub logic {
    my ($self, @values) = @_;
    for (@values) {
        return 0 if $_;
    }
    return 1;
}

sub string {
    my ($self) = @_;
    'none(' . join(', ', map { $_->string } $self->values) . ')';
}

package Class::Multimethods::Pure::Variant;

use Carp;

sub new {
    my ($class, %o) = @_;
    bless {
        params => $o{params} || croak("Multi needs a list of 'params' types"),
        code => $o{code} || croak("Multi needs a 'code'ref"),
    } => ref $class || $class;
}

sub params {
    my ($self) = @_;
    @{$self->{params}};
}

sub code {
    my ($self) = @_;
    $self->{code};
}

sub less {
    my ($a, $b) = @_;

    my @args = $a->params;
    my @brgs = $b->params;
    croak "Multis must have the same number of invocants"
        unless @args == @brgs;
    
    my $proper = 0;
    for my $i (0..$#args) {
        my $cmp = $args[$i]->subset($brgs[$i]);
        return 0 unless $cmp;
        if ($cmp && !$proper) {
            $proper = !$args[$i]->equal($brgs[$i]);
        }
    }

    return $proper;
}

sub matches {
    my ($self, $args) = @_;
    
    my @params = $self->params;
    
    for my $i (0..$#params) {
        unless ($params[$i]->matches($args->[$i])) {
            return 0;
        }
    }
    return 1;
}

sub string {
    my ($self) = @_;
    "(" . join(', ', map { $_->string } $self->params) . ")";
}

package Class::Multimethods::Pure::Method;

use Carp;

sub new {
    my ($class, %o) = @_;
    bless { 
        variants => [], 
        Variant => $o{Variant} || 'Class::Multimethods::Pure::Variant',
        list => undef,
        params => undef,
    } => ref $class || $class;
}

sub add_variant { 
    my ($self, $params, $code) = @_;

    if (defined $self->{params}) {
        croak "Disagreeing number of parameters" if $self->{params} != @$params;
    }
    else {
        $self->{params} = @$params;
    }

    push @{$self->{variants}}, 
        $self->{Variant}->new(params => $params,
                              code => $code);
    undef $self->{vlist};
}

sub compile {
    my ($self) = @_;

    return $self->{vlist} if $self->{vlist};
    
    my @q = 0..@{$self->{variants}}-1;
    my @bin = (0) x @q;

    while (@q) {
        my $i = shift @q;
        
        for my $j (grep { $bin[$_] == $bin[$i] } 0..@{$self->{variants}}-1) {
            if ($self->{variants}[$j]->less($self->{variants}[$i])) {
                $bin[$i]++;
                push @q, $i;
                last;
            }
        }
    }

    my @list;
    for my $i (0..@{$self->{variants}}-1) {
        push @{$list[$bin[$i]]}, $self->{variants}[$i];
    }

    $self->{vlist} = \@list;
    $self->{vlist}
}

sub find_variant {
    my ($self, $args) = @_;

    my $list = $self->compile;

    for my $set (@$list) {
        my @matches = grep { $_->matches($args) } @$set;
        if (@matches == 1) {
            return $matches[0];
        }
        elsif (@matches > 1) {
            croak "Ambiguous method call for args (@$args):\n" .
                join '', map { "    " . $_->string . "\n" } @matches;
        }
    }
    
    croak "No method found for args (@$args)";
}

sub call {
    my $self = shift;

    my $code = $self->find_variant(\@_)->code;
    goto &$code;
}

1;

=head1 TITLE

Class::Multimethods::Pure - Method-ordered multimethod dispatch

=head1 SYNOPSIS

    use Class::Multimethods::Pure;

    package A;
        sub magic { rand() > 0.5 }
    package B;
        use base 'A';
    package C;
        use base 'A';
    
    BEGIN {
        multi foo => ('A', 'A') => sub {
            "Generic catch-all";
        };

        multi foo => ('A', 'B') => sub {
            "More specific";
        };
        
        multi foo => (subtype('A', sub { $_[0]->magic }), 'A') => sub { 
            "This gets called half the time instead of catch-all";
        };

        multi foo => (any('B', 'C'), 'A') => sub {
            "Accepts B or C as the first argument, but not A"
        };
    }

=head1 DESCRIPTION

=head2 Introduciton to Multimethods

When you see the perl expression:

    $animal->speak;

You're asking for C<speak> to be performed on C<$animal>, based on
C<$animal>'s current type.  For instance, if C<$animal> were a Tiger, it
would say "Roar", whereas if C<$animal> were a Dog, it would say "Woof".
The information of the current type of C<$animal> need not be known by
the caller, which is what makes this mechanism powerful.

Now consider a space-shooter game.  You want to create a routine
C<collide> that does something based on the types of I<two> arguments.
For instance, if a Bullet hits a Ship, you want to deliver some damage,
but if a Ship hits an Asteroid, you want it to bounce off.  You could
write it like this:

    sub collide {
        my ($a, $b) = @_;
        if ($a->isa('Bullet') && $b->isa('Ship')) {...}
        elsif ($a->isa('Ship') && $b->isa('Asteroid')) {...}
        ...
    }

Just as you could have written C<speak> that way.  But, above being
ugly, this prohibits the easy addition of new types.  You first have to
create the type in one file, and then remember to add it to this list.

However, there is an analog to methods for multiple arguments, called
I<multimethods>.  This allows the logic for a routine that dispatches on
multiple arguments to be spread out, so that you can include the
relevant logic for the routine in the file for the type you just added.

=head2 Usage

You can define multimethods with the "multi" declarator:

    use Class::Multimethods::Pure;

    multi collide => ('Bullet', 'Ship') => sub {
        my ($a, $b) = @_;  ...
    };

    multi collide => ('Ship', 'Asteroid') => sub {
        my ($a, $b) = @_;  ...
    };

It is usually wise to put such declarations within a BEGIN block, so
they behave more like Perl treats subs (you can call them without
parentheses and you can use them before you define them).

If you think BEGIN looks ugly, then you can define them inline as you
use the module:

    use Class::Multimethods::Pure
        multi => collide => ('Bullet', 'Ship') => sub {...};

But you miss out on a couple of perks if you do that.  See 
L</Special Types> below.

After these are declared, you can call C<collide> like a regular
subroutine:

    collide($ship, $asteroid);

If you defined any variant of a multimethod within a package, then the
multi can also be called as a method on any object of that package (and
any package derived from it). It will be passed as the first argument.

    $ship->collide($asteroid);  # same as above

If you want to allow a multi to be called as a method on some package
without defining any variants in that package, use the null declaration:

    multi 'collide';
    # or
    use Class::Multimethods::Pure multi => collide;

This is also used to import a particular multi into your scope without
defining any variants there.

All multis are global; that is, C<collide> always refers to the same
multi, no matter where/how it is defined.  Allowing scoped multis is on
the TODO list.  But you still have to import it (as shown above) to use
it.

=head2 Non-package Types

In addition to any package name, there are a few special names that
represent unblessed references.  These are the strings returned by
C<ref> when given an unblessed reference.   For the record:

    SCALAR
    ARRAY
    HASH
    CODE
    REF
    GLOB
    LVALUE

For example:

    multi pretty => ('ARRAY') => sub {
        "[ " . join(', ', map { pretty($_) } @{$_[0]}) . " ]";
    };
    multi pretty => ('HASH')  => sub {
        my $hash = shift;
        "{ " . join(', ', 
                map { "$_ => " . pretty($hash->{$_}) } keys %$hash)
        . " }";
    };

=head2 Special Types

There are several types which don't refer to any package.  These are
Junctive types, Any, and Subtypes.

Junctive types represent combinations of types.  C<any('Ship',
'Asteroid')> represents an object that is of either (or both) of the
classes C<Ship> and C<Asteroid>.  C<all('Horse', 'Bird')> represents an
object that is of both types C<Horse> and C<Bird> (probably some sort of
pegasus).  Finally, C<none('Dog')> represents an object that is I<not> a
C<Dog> (or anything derived from C<Dog>).

For example:

    multi fly => ('Horse') => sub { die "Horses don't fly!" };
    multi fly => ('Bird')  => sub { "Flap flap chirp" };
    multi fly => (all('Horse', 'Bird')) => sub { "Flap flap whinee" };

The C<Any> type represents anything at all, object or not.  Use it like
so:

    multi fly => (Any) => sub { die "Most things can't fly." };

Note that it is not a string.  If you give it the string "Any", it will
refer to the C<Any> package, which generally doesn't exist.  C<Any> is a
function that takes no arguments and returns an C<Any> type object.

Finally, there is a C<subtype> function which allows you to specify
constrained types.  It takes two arguments: another type and a code
reference.  The code reference is called on the argument that is being
tested for that type (after checking that the first argument---the base
type---is satisfied), and if it returns true, then the argument is of
that type.  For example:

    my $ZeroOne = subtype(Any, sub { $_[0] < 2 });

We have just defined a type object that is only true when its argument
is less than two and placed it in the type variable C<$ZeroOne>.  Now we
can define the Fibonacci sequence function:

    multi fibo => (Any) => sub { fibo($_[0]-1) + fibo($_[0]-2) };
    multi fibo => ($ZeroOne) => sub { 1 };

Of course, we didn't have to use a type variable; we could have just put
the C<subtype> call right where C<$ZeroOne> appears in the definition.

Consider the follwing declarations:

    multi describe => (subtype(Any, sub { $_[0] > 10 })) => sub {
        "Big";
    };
    multi describe => (subtype(Any, sub { $_[0] == 42 })) => sub {
        "Forty-two";
    };

Calling C<describe(42)> causes an ambiguity error, stating that both
variants of C<describe> match.  We can clearly see that the latter is
more specific than the former (see L</Semantics> for a precise
definition of how this relates to dispatch), but getting the computer to
see that involves solving the halting problem.

So we have to make explicit the relationships between the two subtypes,
using type variables:

    my $Big      = subtype(Any,  sub { $_[0] > 10 });
    my $FortyTwo = subtype($Big, sub { $_[0] == 42 });
    multi describe => ($Big) => sub {
        "Big";
    };
    multi describe => ($FortyTwo) => sub {
        "Forty-two";
    };

Here we have specified that C<$FortyTwo> is more specific than C<$Big>,
since it is a subtype of C<$Big>.  Now calling C<describe(42)> results
in "Forty-two".

In order to get the definitions of C<all>, C<any>, C<none>, C<Any>, and
C<subtype>, you need to import them from the module.  This happens by
default if you use the module with no arguments.  If you only want to
export some of these, use the C<import> command:

    use Class::Multimethods::Pure import => [qw<Any subtype>];

This will accept a null list for you folks who don't like to import
anything.

=head2 Semantics

I've put off explaining the method for determing which method to call
until now.  That's mostly because it will either do exactly what you
want, or yell at you for being ambiguous[1].  I'll take a moment to
define it precisely and mathematically, and then explain what that means
for Mere Mortals.

First, think of a class simply as the set of all of its possible
instances.  When you say C<Foo> is derived from  C<Bar>, you're saying
that "anything that is a C<Foo> is also a C<Bar>", and therefore that
C<Foo> is a subset of C<Bar>.  

Now define a partial order C<< < >> on the variants of a multimethod.
This will represent the relationship "is more specific than".  This is
defined as follows:

Variant A < variant B if and only if

=over

=item * 

Every parameter type in A is a subset of the corresponding parameter in
B.

=item *

At least one of them is a proper subset (that is, a subset but not
equal).

=back

A particular argument list matches a variant A if:

=over

=item *

Each argument is an element of the corresponding parameter type.

=item *

For every variant B, if B matches then A < B.

=back

In other words, we define "is more specific than" in the most
conservative possible terms.  One method is more specific than the other
only when I<all> of its parameters are either equal or more specific.

A couple of notes:

=over

=item * 

Both A and B are more specific than any(A, B), unless one is a subset of
the other, in which case the junction is equivalent the more general
one.

=item *

all(A, B) is more specific than both A and B, unless one is a subset of
the other, in which case the junction is equivalent to the more specific
one.

=item *

A subtype with base type X is always more specific than X.  This is true
even if the constraint is C<sub { 1 }>, unfortunately.  That's one of
those halting problem thingamajiggers.

=item *

Everything is more specific than C<Any>, except C<Any> itself.

=back

[1] Unlike Manhattan Distance as implemented by L<Class::Multimethods>,
which does what you want more often, but does what you don't want
sometimes without saying a word.

=head2 Combinator Factoring

One of the things that I find myself wanting to do most when working
with multimethods is to have combinator types.  These are types that
simply call the multimethod again for some list of aggregated objects
and perform some operation on them (like a Junction). They're easy
to make if they're by themselves.

    multi foo ('Junction', 'Object') {...}
    multi foo ('Object', 'Junction') {...}
    multi foo ('Junction', 'Junction') {...}

However, you find yourself in a major pickle if you want to have more of
them.  For instance:

    multi foo ('Kunction', 'Object') {...}
    multi foo ('Object', 'Kunction') {...}
    multi foo ('Kunction', 'Kunction') {...}

Now they're both combinators, but the module yells at you if you pass
(Kunction, Junction), because there are two methods that would satisfy
that.

The way to define precedence with these combinators is similar to the
way you define precedence in a recursive descent grammar.  You create a
cascade of empty classes at the top of your heirarchy, and derive each
of your generics from a different one of those:

    package AnyObject;
    package JunctionObject;
        use base 'AnyObject';
    package KunctionObject;
        use base 'JunctionObject';
    package Object;
        use base 'KunctionObject';
        # derive all other classes from Object
    
    package Junction;
        use base 'JunctionObject';
        ...
    package Kunction;
        use base 'KunctionObject';
        ...

Now define your multis using these:

    multi foo ('Junction', 'JunctionObject') {...}
    multi foo ('JunctionObject', 'Junction') {...}
    multi foo ('Junction', 'Junction') {...}
    multi foo ('Kunction', 'KunctionObject') {...}
    multi foo ('KunctionObject', 'Kunction') {...}
    multi foo ('Kunction', 'Kunction') {...}

Then the upper one (Junction in this case) will get threaded first,
because a Junction is not a KunctionObject, so it doesn't fit in the
latter three methods.

=head1 AUTHOR

Luke Palmer <lrpalmer@gmail.com>

=head1 COPYRIGHT

Copyright (c) 2005 Luke Palmer.  All rights reserved.
This module is free software.  It may be used, redistributed,
and/or modified under the terms of the Perl Artistic License:
http://www.perl.com/perl/misc/Artistic.html
