package Language::AttributeGrammar;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

use Parse::RecDescent;
use Carp;
use overload ();    # for StrVal (we don't want custom stringifications creeping in)
use Scalar::Util ();

our $VERSION = '0.05';

our $GRAMMAR = <<'#\'EOG';   # mmm, vim hack
#\

{
    # handle whitespace and perl-stype comments
    our $SKIP = qr/(?: \s* (?: \# .*? \n)? )*/x;

    sub massage_code {
        my ($code) = @_;
        $code =~ s/\$\$(?=\W)/\$_AG_SELF/g;
        $code =~ s/\$\.(\w+)/\$_AG_INSTANCE->_AG_LOOKUP(\$_AG_SELF, '$1')/g;
        $code;
    }
}

input: <skip: $SKIP> sem(s?) /\z/
    { [ map { @$_ } @{$item[2]} ] }

sem: classes ':' <leftop: attrdef '|' attrdef>
    {
        [ map {
            { %$_, classes => $item[1] }
          } @{$item[3]} ]
    }
    | <error>

attrdef: attr <perl_codeblock ()> '=' <perl_codeblock>
    {
        {
            attr => $item[1],
            var  => massage_code($item[2]),
            code => massage_code($item[4]),
            line => $thisline,
        }
    }
    | <error>

classes: <leftop: class ',' class>

class: /(?: :: )? \w+ (?: :: \w+ )*/x

attr: /\w+/

#'EOG

our $PARSER = Parse::RecDescent->new($GRAMMAR);

sub new {
    my ($class, $grammar, $grammar2) = @_;   # $grammar becomes $options sometimes
    
    my $options = {};
    if (ref $grammar eq 'HASH') { ($options, $grammar) = ($grammar, $grammar2) }
    
    my $map = $PARSER->input($grammar) or croak "Parse error in grammar";

    # Add prefix to all classes except those that start with ::
    if (exists $options->{prefix}) {
        my $prefix = $options->{prefix};
        carp "Warning: Your prefix doesn't end in ::" unless $prefix =~ /::$/;
        for my $data (@$map) {
            for (@{$data->{classes}}) {
                $_ = "$prefix$_" unless /^::/;
            }
        }
    }
    # strip off all initial ::s.
    for my $data (@$map) {
        s/^::// for @{$data->{classes}};
    }

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
    my $_AG_LINE;
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
                   "    \$_AG_INSTANCE->_AG_INSTALL('$sem->{attr}', $sem->{var}, $sem->{line}, sub {\n".
                   "        \$_AG_LINE = $sem->{line};\n".
                   "        $sem->{code}\n".
                   "    });\n".
                   "}\n";
        my $sub = eval $code or confess "Compile error ($@) in:\n$code";
        push @{$visit{$_}}, $sub for @{$sem->{classes}};
    }

    $_AG_INSTANCE = Language::AttributeGrammar::Instance->new($data, \%visit, \$_AG_LINE);
    $_AG_INSTANCE->_AG_SCAN($data, 'ROOT');
    return $_AG_INSTANCE;
}

package Language::AttributeGrammar::Instance;
# This object represents the runtime engine.

sub new {
    my ($class, $data, $visit, $lineref) = @_;
    my $self = bless {
        cell    => {},
        visit   => $visit,
        data    => $data,
        lineref => $lineref,
    } => ref $class || $class;
}

sub _AG_SCAN {
    # Call all visitors for a given node
    my ($self, $arg, $ref) = @_;
    $ref ||= ref $arg;

    for my $visitor (@{$self->{visit}{$ref} || []}) {
        $visitor->($arg);
    }
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
        $self->_AG_SCAN($arg);
        
        # ... and hope that that caused the cell to be filled in.  If not,
        # we've been given an unsolvable grammar.
        if (my $cell = $self->{cell}{$attr}{$argstr}) {
            $self->_AG_EVAL_CELL($cell);
        }
        else {
            if (defined ${$self->{lineref}}) {
                Carp::croak("A value was demanded for '$attr' ($arg) where none could be provided\n".
                            "near grammar line ${$self->{lineref}}.  Did you try to access an\n".
                            "inherited attribute of the top level of a structure?\n");
            }
            else {
                Carp::croak("Cannot find the attribute '$attr' ($arg) that you asked for.\n");
            }
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
    my ($self, $attr, $arg, $line, $code) = @_;
    my $argstr = overload::StrVal($arg);
    unless ($self->{cell}{$attr}{$argstr}) {
        $self->{cell}{$attr}{$argstr} = {
            thunk => 1,
            value => $code,
        };
    }
    else {
        Carp::croak("Nonlinear attribute: you have two or more ways to assign a value\n".
                    "to the attribute '$attr' near grammar line $line.\n");
    }
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
        Carp::croak("Could not find a way to access '\$.$name' of $obj near grammar line ".
                    "${$self->{lineref}}.\n");
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



=head1 NAME

Language::AttributeGrammar - Attribute grammars for executable syntax trees and other stuff.

=head1 SYNOPSIS

    my $grammar = new Language::AttributeGrammar <<'END_GRAMMAR';
    # find the minimum of a tree from the leaves up
    Leaf:   min($$) = { $.value }
    Branch: min($$) = { List::Util::min(min($.left), min($.right)) }

    # find the global minimum and propagate it back down the tree
    ROOT:   gmin($$)      = { min($$) }
    Branch: gmin($.left)  = { gmin($$) }
          | gmin($.right) = { gmin($$) }

    # reconstruct the tree with every leaf replaced with the minimum value
    Leaf:   result($$)    = { Leaf->new(gmin($$)) }
    Branch: result($$)    = { Branch->new(result($.left), result($.right)) }
    END_GRAMMAR
    
    # This grammar expects that you define these classes:
    #                Branch (with a ->left and ->right attribute)
    #                Leaf   (with a ->value attribute)

    # Use the grammar
    my $tree = Branch->new( Leaf->new(1), 
                            Branch->new( Leaf->new(2), Leaf->new(3)));
                                       
    # Apply the attribute grammar to the data structure
    my $atree = $grammar->apply($tree);
    
    # Fetch synthesized attributes of the root node:
    my $result = $atree->result;   # gives Branch(Leaf(1), Branch(Leaf(1), Leaf(1)));

=head1 DESCRIPTION

This module implements simple (for now) Attribute Grammar support for
Perl data structures.  An attribute grammar is a way to specify
I<computation> over a predefined data structure, say, as generated by
C<Parse::RecDescent>.  This is done by associating I<attributes> with
the nodes of the data structure.

There are two types of attributes: synthesized and inherited.
Synthesized attributes propagate bottom-up, that is, they use
information from the children of a node to infer the attribute's value
on that node.  Inherited attributes are the exact opposite: they use
information from a node in the structure to infer attributes on its
chilren.  

In the example above in the synopsis, the C<min> attribute is
synthesized, since it takes the values at the leaves and infers the
minimum at a branch.  The C<gmin> (global minimum) attribute is
inherited, since it uses C<gmin> that was computed at the root node and
propagates it downward to the leaves.

=head2 Syntax

Some special variables are used in throughout the definitions:

=over

=item * C<$$>

The current node.

=item * C<$.foo>

The child node named C<foo> of the current node.

=back

The grammar definition is composed of a series of I<semantics>
definitions.  An example semantic definition is:

    Foo, Bar: baz($$)       = { baz($.child) }
            | quux($.child) = { quux($$) }

This specifies the implementations of the I<synthesized attribute>
C<baz> and the I<inherited attribute> C<quux> for nodes of type Foo and
Bar.  That is, you can find the C<baz> attribute of the current node by
looking at the baz attribute of its child, and you can find the C<quux>
attribute of any node's child by looking at the C<quux> attribute of the
node itself.

The C<$.child> notation is defined to pretty much do the right thing.
But, in the name of predictability, here are the semantics:

If C<$$> has a method named C<child> (for the attribute C<$.child>),
then that method is called with no arguments to fetch the attribute.
Otherwise, if C<$$> is a blessed hash, then the module snoops inside the
hash and pulls out the key named "child".  If the hash has no such key,
or the object is not a blessed hash (eg. a blessed array), then we
give up.

If your tree has a different convention for extracting child nodes, you can
always use C<$$> explicitly:

    Cons:  sum($$) = { $$->get_child('head') + sum($$->get_child('tail')) }
    Nil:   sum($$) = { 0 }

    Cons:  gsum($$->get_child('head')) = { gsum($$) }

In the future I may provide a callback that allows the user to define
the meaning of C<$.child>.

There is one special class name that can go to the left of the colon:
C<ROOT>.  This represents the root of the data structure you were given,
and is used to avoid the common annoyance of creating a Root node
class tha just bootstraps the "real" tree.   So when you say:

    ROOT:  gmin($$) = { min($$) }

That means that when you're at the root of the data structure, the
global minimum is equal to the local minimum.

=head2 Usage

After you have a grammar specification in a string, create a new grammar
object:

    my $grammar = Language::AttributeGrammar->new($grammar_string);

This contains a minimal data structure of the semantics definitions.  The 
constructor also can take an options hash as its first argument:

    my $grammar = Language::AttributeGrammar->new({ prefix => 'Foo::' }, $grammar_string);

The only option at the moment is C<prefix>, which will prepend this
prefix to all the types mentioned in your grammar.  However, if you need
to omit this prefix, name the type in your grammar starting with a
C<::>, and the prefix will not be prepended.

In order to use it on a data structure, C<apply> it to the data
structure:

    my $attr_data = $grammar->apply($data);

This is not the data structure in any form, really.  It's just an object
on which you can call methods to fetch attributes on the I<top node> of
C<$data>.  To get the "min" attribute on C<$data>, call:

    my $min = $attr_data->min;

In order to find attributes on nodes that are lower in the structure,
you must concoct your attribute grammar to propagate that information up
the tree somehow.  Usually this is done using a synthesized attribute
that mirrors the given data structure.

This module is designed to be used I<functionally>, that is, you
shouldn't change the data structure or any global state within the
definitions.  Instead, return a new data structure with the information
you need embedded in it.

=head1 AUTHOR

Luke Palmer <lrpalmer gmail com>

=head1
