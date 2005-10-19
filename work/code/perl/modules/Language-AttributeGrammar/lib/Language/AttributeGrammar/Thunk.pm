package Language::AttributeGrammar::Thunk;

use Carp;
use Perl6::Attributes;

# three-stage thunk
#   stage 1: code unset
#   stage 2: code set, unevaluated
#   stage 3: code evaluated and return value stored

sub new {
    my ($class, $code, $attr, $at) = @_;
    my $self = bless {
        stage => ($code ? 2 : 1),
        code  => $code,
        value => undef,
        attr  => $attr,
        at    => $at,
    } => ref $class || $class;
    $self;
}

sub set {
    my ($self, $code, $attr, $at) = @_;
    unless ($.stage == 1) {
        croak "Attribute '$attr' defined more than once at $at and $.at";
    }
    $.at = $at;
    $.code = $code;
    $.stage++;
}

sub get {
    my ($self, $attr, $at) = @_;
    if ($.stage == 3) {
        $.value;
    }
    elsif ($.stage == 2) {
        $.value = $.code->();
        undef $.code;
        $.stage++;
        $.value;
    }
    else {
        croak "Attribute '$attr' not defined at $at";
    }
}

1;
