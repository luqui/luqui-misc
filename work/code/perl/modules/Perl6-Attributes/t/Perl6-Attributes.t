use Test::More tests => 6;

BEGIN { use_ok('Perl6::Attributes') };

is(q($.foo), q($self->{'foo'}), 'scalar');
is(q(@.foo), q(@{$self->{'foo'}}), 'array');
is(q(%.foo), q(%{$self->{'foo'}}), 'hash');
is(q(&.foo), q(&{$self->{'foo'}}), 'code');
is(q($.x),   q($self->{'x'}), 'single letter');

# vim: ft=perl :
