package Class::Multimethods::Pure;

use 5.006001;
use strict;
use warnings;
no warnings 'undefined';

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
        name => $o{name} || croak "Multi needs a 'name'",
        params => $o{params} || croak "Multi needs a list of 'params' types",
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
        
    my @args = $a->args;
    my @brgs = $b->args;
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
        name => $o{name} || croak "Multi needs a name",
        variants => [], 
        Dispatcher => $o{Dispatcher} || 'Class::Multimethods::Pure::Dispatcher',
        Variant => $o{Variant} || 'Class::Multimethods::Pure::Variant',
        graph => undef,
    } => ref $class || $class;
}

sub add_variant { 
    my ($self, $code, $args, %o) = @_;
    push @{$self->{variants}}, 
        $self->{Variant}->new(name => $self->{name}, 
                              args => $args,
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
    my @vars = _find_variant_find($graph, $args);
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
