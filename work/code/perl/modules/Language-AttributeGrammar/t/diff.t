use Test::More tests => 2;

BEGIN { use_ok('Language::AttributeGrammar::Lazy') }

my $grammar = new Language::AttributeGrammar::Lazy <<'EOG';

Cons: len($$)     = { 1 + len($.tail) }   # length of list is 1 + length of tail
Nil:  len($$)     = { 0 }

Cons: sum($$)     = { $.head + sum($.tail) }
Nil:  sum($$)     = { 0 }

Root: avg($.list) = { sum($.list) / len($.list) }
Cons: avg($.tail) = { avg($$) }

Root: diff($$)    = { diff($.list) }
Cons: diff($$)    = # Cons($.head - avg($$), diff($.tail))
    {
        bless { head => ($.head - avg($$)), tail => diff($.tail) } => 'Cons' 
    }
Nil:  diff($$)    = { bless { } => 'Nil' }

EOG

sub Root { bless { list => $_[0] } => 'Root' }
sub list { 
    if (@_) {
        bless { head => $_[0], tail => list(@_[1..$#_]) } => 'Cons';
    }
    else {
        bless { } => 'Nil';
    }
}

my $atree = $grammar->apply(Root(list(1,2,3,4,5)));
is_deeply($atree->diff, list(-2,-1,0,1,2));

# vim: ft=perl :
