package Language::AttributeGrammar::Engine;

use strict;
use warnings;
no warnings 'uninitialized';

use Carp;
use Perl6::Attributes;
use Language::AttributeGrammar::Thunk;

sub new {
    my ($class) = @_;
    bless {
        cases => {},
    } => ref $class || $class;
}

sub add_visitor {
    my ($self, $case, $visitor) = @_;
    push @{$.cases{$case}{visit}}, $visitor;
}

sub make_visitor {
    my ($self, $visit) = @_;
    
    for my $case (keys %.cases) {
        $.cases{$case}{visit_all} = sub {
            $_->(@_) for @{$.cases{$case}{visit}};
        };
        next if $case eq 'ROOT';
        no strict 'refs';
        *{"$case\::$visit"} = $.cases{$case}{visit_all};
    }
}

sub annotate {
    my ($self, $visit, $top) = @_;
    print "Annotating...\n";
    my @nodeq;
    my $attrs = Language::AttributeGrammar::Engine::Vivifier->new(sub {
                    push @nodeq, $_[0];
                    Language::AttributeGrammar::Engine::Vivifier->new(sub {
                        Language::AttributeGrammar::Thunk->new;
                    });
                });

    $attrs->get($top);   # seed the queue
                
    if ($.cases{ROOT}{visit_all}) {
        $.cases{ROOT}{visit_all}->($top, $attrs);
    }

    while (my $node = shift @nodeq) {
        $node->$visit($attrs);
    }

    return $attrs;
}

sub evaluate {
    my ($self, $visit, $top, $attr) = @_;
    my $attrs = $self->annotate($visit, $top);
    my $head = $attrs->get($top)->get($attr);
    undef $attrs;   # allow intermediate values to go away
    print "Evaluating...\n";
    $head->get;
}

package Language::AttributeGrammar::Engine::Vivifier;

use overload ();

sub new {
    my ($class, $vivi) = @_;
    bless {
        hash => {},
        vivi => $vivi,
    } => ref $class || $class;
}

sub get {
    my ($self, $key) = @_;
    unless (exists $.hash{$key}) {
        $.hash{overload::StrVal($key)} = $.vivi->($key);
        print "Vivified $.hash{overload::StrVal($key)}\n";
        $.hash{overload::StrVal($key)};
    }
    else {
        $.hash{overload::StrVal($key)};
    }
}

sub put {
    my ($self, $key, $value) = @_;
    $.hash{overload::StrVal($key)} = $value;
}

sub keys {
    my ($self) = @_;
    keys %.hash;
}

1;
