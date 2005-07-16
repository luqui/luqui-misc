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
                push @params, shift;
            }
        }
        
        return () unless @_;
        
        my $code = shift;

        my $multi = $MULTI{$name} ||= 
                Class::Multimethods::Pure::Method->new(
                    name => $name,
                    Dispatcher => $MULTIPARAM{$name}{Dispatcher},
                    Variant => $MULTIPARAM{$name}{Variant},
                );
        
        $multi->add_variant($code, \@params);
    }

    my $pkg = caller 2;
    {
        no strict 'refs';
        no warnings 'redefine';
        *{"$pkg\::$name"} = sub {
            my $code = $MULTI{$name}->find_variant([@_])->code;
            goto &$code;
        };
    }
    
    @_;
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

package Class::Multimethods::Pure::Dispatcher;

use Scalar::Util qw<blessed looks_like_number>;

our %SPECIAL = (
    '#'    => 1,
    '$'    => 1,
    '*'    => 1,
    SCALAR => 1,
    ARRAY  => 1,
    HASH   => 1,
    CODE   => 1,
    REF    => 1,
    GLOB   => 1,
    LVALUE => 1,
);

sub new {
    my ($class) = @_;
    $class;
}

sub subset {
    my ($self, $classa, $classb) = @_;
    
    return (1, 0) if $classa eq $classb;

    if ($SPECIAL{$classa} || $SPECIAL{$classb}) {
        return (1, 1) if $classb eq '*';
        return (1, 1) if $classa eq '#' && $classb eq '$';
    }
    else {
        return (1, 1) if $classa->isa($classb);
    }

    return (0, 0);
}

sub matches {
    my ($self, $obj, $class) = @_;
    
    return 1 if $class eq '*';
    
    if (ref $obj) {
        if (blessed $obj) {
            $obj->isa($class);
        }
        else {
            ref $obj eq $class;
        }
    }
    else {
        $class eq '$' || ($class eq '#' && looks_like_number($obj));
    }
}

sub string {
    my ($self, $class) = @_;
    $class;
}

package Class::Multimethods::Pure::Variant;

use Carp;

sub new {
    my ($class, %o) = @_;
    bless {
        name => $o{name} || croak("Multi needs a 'name'"),
        params => $o{params} || croak("Multi needs a list of 'params' types"),
        code => $o{code} || croak("Multi needs a 'code'ref"),
        Dispatcher => $o{Dispatcher} || 'Class::Multimethods::Pure::Dispatcher',
    } => ref $class || $class;
}

sub name {
    my ($self) = @_;
    $self->{name};
}

sub params {
    my ($self) = @_;
    @{$self->{params}};
}

sub code {
    my ($self) = @_;
    $self->{code};
}

sub Dispatcher {
    my ($self) = @_;
    $self->{Dispatcher};
}

sub less {
    my ($a, $b) = @_;
    croak "Variants from different multis do not compare"
        unless $a->name eq $b->name;
        
    my $dispatcher = $a->Dispatcher;
    croak "Cannot compare two variants with different dispatchers"
        unless $dispatcher eq $b->Dispatcher;
        
    my @args = $a->params;
    my @brgs = $b->params;
    croak "Multis must have the same number of invocants"
        unless @args == @brgs;
    
    my $proper = 0;
    for my $i (0..$#args) {
        my ($cmp, $isproper) = $dispatcher->subset($args[$i], $brgs[$i]);
        return 0 unless $cmp;
        $proper = 1 if $isproper;
    }

    return $proper;
}

sub matches {
    my ($self, $args) = @_;
    
    my @params = $self->params;
    
    for my $i (0..$#params) {
        unless ($self->Dispatcher->matches($args->[$i], $params[$i])) {
            return 0;
        }
    }
    return 1;
}

sub string {
    my ($self) = @_;
    $self->name . "(" . join(', ', 
        map { $self->Dispatcher->string($_) } $self->params) . ")";
}

package Class::Multimethods::Pure::Method;

use Carp;

sub new {
    my ($class, %o) = @_;
    bless { 
        name => $o{name} || croak("Multi needs a name"),
        variants => [], 
        Dispatcher => $o{Dispatcher} || 'Class::Multimethods::Pure::Dispatcher',
        Variant => $o{Variant} || 'Class::Multimethods::Pure::Variant',
        graph => undef,
        params => undef,
    } => ref $class || $class;
}

sub add_variant { 
    my ($self, $code, $params) = @_;

    if (defined $self->{params}) {
        croak "Disagreeing number of parameters" if $self->{params} != @$params;
    }
    else {
        $self->{params} = @$params;
    }

    push @{$self->{variants}}, 
        $self->{Variant}->new(name => $self->{name}, 
                              params => $params,
                              code => $code,
                              Dispatcher => $self->{Dispatcher});
    undef $self->{graph};
}

sub _compile_make_node {
    my ($self, $variant, $cache, $fathered) = @_;

    return $cache->{$variant} if $cache->{$variant};
    
    my @children;
    for (@{$self->{variants}}) {
        if ($variant->less($_)) {
            my $child = $self->_compile_make_node($_, $cache, $fathered);
            push @children, $child;
            $fathered->{$child} = 1;
        }
    }
    
    $cache->{$variant} = {
        value => $variant,
        children => \@children,
    };
}

sub compile {
    my ($self) = @_;
    
    return $self->{graph} if $self->{graph};
    
    my ($fathered, $cache) = ({}, {});
    my @nodes = map { $self->_compile_make_node($_, $cache, $fathered) }
                    @{$self->{variants}};
    
    my @heads = grep { !$fathered->{$_} } @nodes;
    confess "Ack! No heads!" unless @heads;

    my $head = {
        value => undef,
        children => \@heads,
    };

    $self->{graph} = $head;
}

sub _find_variant_find {
    my ($self, $node, $args) = @_;
    
    if (my $var = $node->{value}) {
        return $var if $var->matches($args);
    }

    map { $self->_find_variant_find($_, $args) } @{$node->{children}};
}

sub find_variant {
    my ($self, $args) = @_;

    my $graph = $self->compile;
    my @vars = $self->_find_variant_find($graph, $args);
    if (@vars == 1) {
        return $vars[0];
    }
    elsif (@vars == 0) {
        croak "No method found for args (@$args)";
    }
    else {
        croak "Ambiguous method call for args (@$args):\n" .
            join '', map { "    " . $_->string . "\n" } @vars;
    }
}

1;
