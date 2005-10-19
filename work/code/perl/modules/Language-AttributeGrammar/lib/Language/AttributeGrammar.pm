package Language::AttributeGrammar;

use 5.006001;
use strict;
use warnings;
no warnings 'uninitialized';

our $VERSION = '0.07';

use Language::AttributeGrammar::Parser;
use Perl6::Attributes;

my $methnum = '0';

sub new {
    my ($class, $options, $grammar) = @_;
    $grammar = $options unless ref $options eq 'HASH';

    my $engine = Language::AttributeGrammar::Parser->new($grammar);
    my $meth = '_AG_visit_' . $methnum++;
    $engine->make_visitor($meth);
    
    bless {
        engine => $engine,
        meth   => $meth,
    } => ref $class || $class;
}

sub apply {
    my ($self, $top, $attr) = @_;

    $.engine->evaluate($.meth, $top, $attr);
}

sub annotate {
    my ($self, $top) = @_;
    Language::AttributeGrammar::Annotator->new($.engine->annotate($.meth, $top));
}

package Language::AttributeGrammar::Annotator;

sub new {
    my ($class, $ann) = @_;

    bless {
        ann => $ann,
    } => ref $class || $class;
}

our $AUTOLOAD;
sub AUTOLOAD {
    (my $attr = $AUTOLOAD) =~ s/.*:://;
    return if $attr eq 'DESTROY';

    my ($self, $node) = @_;
    $self->get($node)->get($attr)->get;
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
