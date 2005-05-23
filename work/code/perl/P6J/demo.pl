# BEGIN { $DB::single=1 }
use Perl6::Junctions qw{CORE::int CORE::substr};
use Data::Dumper 'Dumper';

my $x = all(1,2,3);
my $y = 4|5|6;
my $z = none(4,5,6);

if ($x<4)    { print "all(1,2,3) < 4\n" }
if ($y==4)   { print "any(4,5,6) == 4\n" }

if ($z>4)     { print "none(4,5,6) > 4\n" }
if ($z>5)     { print "none(4,5,6) > 5\n" }
if ($z>6)     { print "none(4,5,6) > 6\n" }

$z = $x + $y;

if ($z>10)    { print "all(1,2,3)+any(4,5,6) > 10\n" }
if ($z<10)    { print "all(1,2,3)+any(4,5,6) < 10\n" }

if ($z>4)    { print "all(1,2,3)+any(4,5,6) > 4\n" }
if ($z<4)    { print "all(1,2,3)+any(4,5,6) < 4\n" }


if (sin all(1,2,3,4,5,6) < 1 ) { print "all sins are less than 1\n" }

if ((1&2|3&4) < 4) { print "true 9b\n" }
if ((9&2|3&4) < 4) { print "true 9c\n" }

if ((10^2^5) < 4)  { print "one(10,2,5)  < 4\n" }
if ((1^2^5) < 4)   { print "one(1^2^5)   < 4\n" }
if ((10^11^5) < 4) { print "one(10^11^5) < 4\n" }

my $seen = any();
my $oddline = ("line "|"Line ") . (1|3) . "\n";

while (<DATA>) {
	next if $_ eq $seen;
	$seen |= $_;
	print;
	print "\t(that's odd)\n" if $_ eq $oddline;
}

my $subs = any(sub{print "calling sub A\n"},
	       sub{print "calling sub B\n"},
	       sub{print "calling sub C\n"},
	      );

$subs->();
 
package ClassA;
sub new { bless {}, $_[0] }
sub method { print "ClassA::method()\n" }

package ClassB;
sub new { bless {}, $_[0] }
sub method { print "ClassB::method()\n" }

package main;
('ClassA'|'ClassB')->new->method();

__DATA__
line 1
line 2
line 1
line 2
line 3
Line 1
line 4
