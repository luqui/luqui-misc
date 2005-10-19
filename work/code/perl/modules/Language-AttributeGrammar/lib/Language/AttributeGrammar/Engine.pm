package Language::AttributeGrammar::Engine;

use strict;
use warnings;
no warnings 'uninitialized';

use Carp;
use Perl6::Attributes;
use Language::AttributeGrammar::Thunk;

use Devel::STDERR::Indent qw<indent>;

sub new {
    my ($class) = @_;
    bless {
        cases => {},
    } => ref $class || $class;
}

sub add_case {
    my ($self, $case) = @_;
    $.cases{$case}{visit} ||= [];
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
        if ($node->can($visit)) {
            $node->$visit($attrs);
        }
        else {
            croak "No case defined: " . ref($node) . "\n";
        }
    }

    return $attrs;
}

sub evaluate {
    my ($self, $visit, $top, $attr) = @_;
    my $attrs = $self->annotate($visit, $top);
    my $head = $attrs->get($top)->get($attr);
    undef $attrs;   # allow intermediate values to go away
    $head->get($attr, 'top level');
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
    my $kval = overload::StrVal($key);
    unless (exists $.hash{$kval}) {
        $.hash{$kval} = $.vivi->($key);
        $.hash{$kval};
    }
    else {
        $.hash{$kval};
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
