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

    my $pkg = caller 2;
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
        croak "Usage: blah blah blah";
    }
}

sub import {
    my $class = shift;
    if (@_) {
        while (@_ = _internal_multi(@_)) { }
    }
    else {
        my $pkg = caller;
        no strict 'refs';
        *{"$pkg\::multi"} = \&multi;
    }
}

package Class::Multimethods::Pure::Type;

use Carp;

my $SUBSET = Class::Multimethods::Pure::Method->new;

sub subset {
    my ($self, $other) = @_;
    $SUBSET->call($self, $other);
}

my $EQUAL = Class::Multimethods::Pure::Method->new;

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
             0;
    });
    
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
        [ $pkg->('Type::Junction'), $pkg->('Type') ] => sub {
             my ($a, $b) = @_;
             $a->logic(map { $_->subset($b) } $a->values);
    });

    $SUBSET->add_variant(
        [ $pkg->('Type'), $pkg->('Type::Junction') ] => sub {
             my ($a, $b) = @_;
             $b->logic(map { $a->subset($_) } $b->values);
    });

    # :-( disambiguator.  Turns out leftmost (or rightmost) would be just fine here.
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
        [ $pkg->('Type::Junction'), $pkg->('Type') ] => sub {
            my ($a, $b) = @_;
            $a->logic(map { $_->equal($b) } $a->values);
    });

    $EQUAL->add_variant(
        [ $pkg->('Type'), $pkg->('Type::Junction') ] => sub {
            my ($a, $b) = @_;
            $b->logic(map { $a->equal($_) } $b->values);
    });

    # disambiguator.  See above.
    $EQUAL->add_variant(
        [ $pkg->('Type::Junction'), $pkg->('Type::Junction') ] => sub {
            my ($a, $b) = @_;
            # same as (Junction, Type)
            $a->logic(map { $_->equal($b) } $a->values);
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

# This is overridden for bootstrapping purposes.
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

package Class::Multimethods::Pure::Type::Unblessed;

# SCALAR, ARRAY, etc.
use base 'Class::Multimethods::Pure::Type';
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
        type => $name,
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
