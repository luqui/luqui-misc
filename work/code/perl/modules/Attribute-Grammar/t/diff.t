use Test::More tests => 3;

BEGIN { use_ok('Attribute::Grammar') }

my $grammar = new Attribute::Grammar <<'EOG';

Cons: len($$)     = { 1 + len($.tail) }
Nil:  len($$)     = { 0 }

Cons: sum($$)     = { $.head + sum($.tail) }
Nil:  sum($$)     = { 0 }

Root: avg($.tree) = { sum($.tree) / len($.tree) }
Cons: avg($.tail) = { avg($$) }

Root: diff($$)    = { diff($.tree) }
Cons: diff($$)    = { bless { head => ($.head - avg($$)), tail => diff($.tail) } => 'Cons' }
Nil:  diff($$)    = { bless { } => 'Nil' }

EOG

sub Root { bless { tree => $_[0] } => 'Root' }
sub list { 
    if (@_) {
        bless { head => $_[0], tail => list(@_[1..$#_]) } => 'Cons';
    }
    else {
        bless { } => 'Nil';
    }
}

my $atree = $grammar->apply(Root(list(1,2,3,4,5)));
is($atree->avg, 3, "avg worked");
is_deeply($atree->diff, list(-2,-1,0,1,2));

# vim: ft=perl :
