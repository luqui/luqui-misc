use Perl6::Junctions;

sub sanitized {
    my ($val) = @_;
    my $dumped = eval { $val->dump };
    return $dumped if defined $dumped;
    return $val;
}

my $j = 1|none(2)|all(3,4);

# All (non-junctive) values that junction contains
# and which also match junction itself...

for my $value ($j->values) {
    print "$value\n";
}

print "===========\n";

# String representation of junction..

print $j->dump, "\n";

print "===========\n";


# Random seclection of one state (not value!) from junction..

for (1..10) {
    print sanitized($j->pick), "\n";
}

print "===========\n";


# List of top-level components of junction
# (which may themselves be junctive, as here)

for my $state ($j->states) {
    print sanitized($state), "\n";
}

print "===========\n";


# Crash and burn...

print $j;
