package Language::AttributeGrammar::Thunk;

use Carp;
use Perl6::Attributes;

# three-stage thunk
#   stage 1: code unset
#   stage 2: code set, unevaluated
#   stage 3: code evaluated and return value stored

sub new {
    my ($class, $code) = @_;
    my $self = bless {
        stage => ($code ? 2 : 1),
        code  => $code,
        value => undef,
    } => ref $class || $class;
    $self;
}

sub set {
    my ($self, $code) = @_;
    unless ($.stage == 1) {
        croak "Bad attempt to set code for stage-2 or stage-3 thunk";
    }
    $.code = $code;
    $.stage++;
}

sub get {
    my ($self) = @_;
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
        croak "Bad attempt to evaluate stage-1 thunk";
    }
}

1;
