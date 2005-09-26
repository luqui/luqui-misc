package Language::AttributeGrammar;

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

{
    # handle whitespace and perl-stype comments
    our $SKIP = qr/(?: \s* (?: \# .*? \n)? )*/x;
}

input: <skip: $SKIP> sem(s?) /\z/
    { [ map { @$_ } @{$item[2]} ] }

sem: classes ':' <leftop: attrdef '|' attrdef>
    {
        [ map {
            { %$_, classes => $item[1] }
          } @{$item[3]} ]
    }

attrdef: attr '(' var ')' '=' <perl_codeblock>
    {
        my $code = $item[6];
        $code =~ s/\$\$(?=\W)/\$_AG_SELF/g;
        $code =~ s/\$\.(\w+)/\$_AG_INSTANCE->_AG_LOOKUP(\$_AG_SELF, '$1')/g;
        
        {
            attr => $item[1],
            var  => $item[3],
            code => $code,
        }
    }

classes: <leftop: class ',' class>

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

    my @attrs = map { $_->{attr} } @$map;
    
    bless {
        attrs => \@attrs,
        map => $map,
    } => ref $class || $class;
}

my $packageno = '000000';

# Apply takes the list of sems (from $self) and generates a ::Instance object.
# This is the heavy compilation side function.
sub apply {
    no strict 'refs';

    my ($self, $data) = @_;
    my $_AG_INSTANCE;   # we refer to this from within the generated code
    my $package = "Language::AttributeGrammar::ANON" . $packageno++;

    # Generate the accessor functions for the attributes.  When you say
    # min($.left) in the body, this is what it calls.
    my %seen;
    for my $attr (@{$self->{attrs}}) {
        next if $seen{$attr}++;
        *{"$package\::$attr"} = sub { 
            my ($arg) = @_;
            $_AG_INSTANCE->_AG_VISIT($attr, $arg);
        }
    }

    # Generate the visitor code.  When it visits a node, it runs through the visitors
    # in $visit{ref $node} and calls them all.  Each visitor installs a thunk of its
    # body into the $attr:$node slot.  See _AG_INSTALL and _AG_VISIT.
    my %visit;
    for my $sem (@{$self->{map}}) {
        my $code = "package $package;  use strict;\n".
                   "sub {\n".
                   "    my (\$_AG_SELF) = \@_;\n".
                   "    \$_AG_INSTANCE->_AG_INSTALL('$sem->{attr}', $sem->{var}, sub $sem->{code});\n".
                   "}\n";
        my $sub = eval $code or confess "Compile error ($@) in:\n$code";
        push @{$visit{$_}}, $sub for @{$sem->{classes}};
    }

    $_AG_INSTANCE = Language::AttributeGrammar::Instance->new($data, \%visit);
}

package Language::AttributeGrammar::Instance;
# This object represents the runtime engine.

sub new {
    my ($class, $data, $visit) = @_;
    my $self = bless {
        cell => {},
        visit => $visit,
        data => $data,
    } => ref $class || $class;
}

# Whenever you see min($.left), that's a call to $_AG_INSTANCE->_AG_VISIT('min', $.left).
sub _AG_VISIT {
    my ($self, $attr, $arg) = @_;
    my $argstr = overload::StrVal($arg);

    # If a thunk has already been installed in the cell we are trying,
    # just evaluate the thunk.
    if (my $cell = $self->{cell}{$attr}{$argstr}) {
        $self->_AG_EVAL_CELL($cell);
    }
    else {
        # Otherwise, call each visitor for this node on this node...
        for my $visitor (@{$self->{visit}{ref $arg}}) {
            $visitor->($arg);
        }
        
        # ... and hope that that caused the cell to be filled in.  If not,
        # we've been given an unsolvable grammar.
        if (my $cell = $self->{cell}{$attr}{$argstr}) {
            $self->_AG_EVAL_CELL($cell);
        }
        else {
            Carp::croak("A value was demanded for $attr($arg) where none could be provided\n".
                        "(possibly you tried to evaluate an inherited attribute on the root node?)");
        }
    }
}

# Evaluate a thunk.
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

# Install a thunk in a particular attribute slot of a particular object.
sub _AG_INSTALL {
    my ($self, $attr, $arg, $code) = @_;
    my $argstr = overload::StrVal($arg);
    $self->{cell}{$attr}{$argstr} = {
        thunk => 1,
        value => $code,
    };
}

# This determines the semantics of $.attr.
sub _AG_LOOKUP {
    my ($self, $obj, $name) = @_;
    # If it has a method with the name of the attribute, we'll use it (support
    # encapsulation if we can).
    if (Scalar::Util::blessed($obj) && $obj->can($name)) {
        $obj->$name;
    }
    # Otherwise look inside the hash and see if it has that key.
    elsif (Scalar::Util::reftype($obj) eq 'HASH' && exists $obj->{$name}) {
        $obj->{$name};
    }
    else {
        Carp::croak("Could not find a way to access \$.$name of $obj");
    }
}

# This lets us access attributes of the root node from the outside world.
our $AUTOLOAD;
sub AUTOLOAD {
    my ($self) = @_;
    (my $name = $AUTOLOAD) =~ s/.*:://;
    return if $name eq 'DESTROY';
    $self->_AG_VISIT($name, $self->{data});
}

1;
