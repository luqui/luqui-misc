use Perl6::Junctions;
use Data::Dumper 'Dumper';

my $x = all(1,2);
my $y = 4|5;

print +($x+$y)->dump, "\n";
print +($y+$x)->dump, "\n";
