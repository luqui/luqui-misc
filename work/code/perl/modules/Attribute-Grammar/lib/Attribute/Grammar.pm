package Attribute::Grammar;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

use Parse::RecDescent;
use Carp;
use overload ();    # for StrVal (we don't want custom stringifications creeping in)
use Scalar::Util ();

our $GRAMMAR = <<'#\'EOG';   # mmm, vim hack
#\
input: sem(s?) /\z/
    {
        my %result;
        for my $sem (@{$item[1]}) {
            push @{$result{$sem->{class}}}, $sem->{data};
        }
        \%result;
    }

sem: class ':' attr '(' var ')' '=' <perl_codeblock>
    {
        my $code = $item[8];
        $code =~ s/\$\$(?=\W)/\$_AG_SELF/g;
        $code =~ s/\$\.(\w+)/\$_AG_INSTANCE->_AG_LOOKUP(\$_AG_SELF, '$1')/g;
        
        {
            class => $item[1],
            data => { 
                attr => $item[3],
                var  => $item[5],
                code => $code,
            },
        }
    }

class: /\w+ (?: :: \w+ )*/x

attr: /\w+/

var: '$$'
    { '$_AG_SELF' }
   | /\$\.\w+/
    { 
        my ($name) = $item[1] =~ /^\$\.(\w+)$/;
        "\$_AG_INSTANCE->_AG_LOOKUP(\$_AG_SELF, '$name')";
    }

#'EOG

our $PARSER = Parse::RecDescent->new($GRAMMAR);

sub new {
    my ($class, $grammar) = @_;
    my $map = $PARSER->input($grammar) or croak "Error in grammar";

    my @attrs;
    for (values %$map) {
        push @attrs, map { $_->{attr} } @$_;
    }
    
    bless {
        attrs => \@attrs,
        map => $map,
    } => ref $class || $class;
}

my $packageno = '000000';
sub apply {
    no strict 'refs';

    my ($self, $data) = @_;
    my $_AG_INSTANCE;
    my $package = "Attribute::Grammar::ANON" . $packageno++;
    my %seen;
    for my $attr (@{$self->{attrs}}) {
        next if $seen{$attr}++;
        *{"$package\::$attr"} = sub { 
            my ($arg) = @_;
            $_AG_INSTANCE->_AG_VISIT($attr, $arg);
        }
    }

    my %visit;
    for my $class (keys %{$self->{map}}) {
        for my $data (@{$self->{map}{$class}}) {
            my $code = "package $package;  use strict;\n".
                       "sub {\n".
                       "    my (\$_AG_SELF) = \@_;\n".
                       "    \$_AG_INSTANCE->_AG_INSTALL('$data->{attr}', $data->{var}, sub $data->{code});\n".
                       "}\n";
            my $sub = eval $code or confess "Compile error ($@) in:\n$code";
            push @{$visit{$class}}, $sub;
        }
    }

    $_AG_INSTANCE = Attribute::Grammar::Instance->new($data, \%visit);
}

package Attribute::Grammar::Instance;

sub new {
    my ($class, $data, $visit) = @_;
    my $self = bless {
        cell => {},
        visit => $visit,
        data => $data,
    } => ref $class || $class;
}

sub _AG_VISIT {
    my ($self, $attr, $arg) = @_;
    my $argstr = overload::StrVal($arg);
    if (my $cell = $self->{cell}{$attr}{$argstr}) {
        $self->_AG_EVAL_CELL($cell);
    }
    else {
        for my $visitor (@{$self->{visit}{ref $arg}}) {
            $visitor->($arg);
        }
        
        if (my $cell = $self->{cell}{$attr}{$argstr}) {
            $self->_AG_EVAL_CELL($cell);
        }
        else {
            Carp::croak("A value was demanded for $attr($arg) where none could be provided\n".
                        "(possibly you tried to evaluate an inherited attribute on the root node?)");
        }
    }
}

sub _AG_EVAL_CELL {
    my ($self, $cell) = @_;
    if ($cell->{thunk}) {
        $cell->{thunk} = 0;
        $cell->{value} = $cell->{value}->();
    }
    else {
        $cell->{value};
    }
}

sub _AG_INSTALL {
    my ($self, $attr, $arg, $code) = @_;
    my $argstr = overload::StrVal($arg);
    $self->{cell}{$attr}{$argstr} = {
        thunk => 1,
        value => $code,
    };
}

sub _AG_LOOKUP {
    my ($self, $obj, $name) = @_;
    if (Scalar::Util::blessed($obj) && $obj->can('name')) {
        $obj->name;
    }
    elsif (Scalar::Util::reftype($obj) eq 'HASH' && exists $obj->{$name}) {
        $obj->{$name};
    }
    else {
        Carp::croak("Could not find a way to access \$.$name of $obj");
    }
}

our $AUTOLOAD;
sub AUTOLOAD {
    my ($self) = @_;
    (my $name = $AUTOLOAD) =~ s/.*:://;
    return if $name eq 'DESTROY';
    $self->_AG_VISIT($name, $self->{data});
}

1;
