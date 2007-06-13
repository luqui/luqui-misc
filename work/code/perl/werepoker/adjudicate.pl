#!/usr/bin/perl

use strict;
use CGI ();
use DBI ();

my %algorithms = (
    'Algorithm::Munkres' => 1,
    'BidPicker' => 1,
);

my $dbh = DBI->connect('DBI:mysql:werepoker', 'fibonaci', 'sre-piz',
                        { RaiseError => 1, AutoCommit => 0 })
            or die "Couldn't connect to database: " . DBI->errstr;

my $cgi = CGI->new;

my $gamename = $cgi->param('gamename');
die "Malformed game name" unless $gamename =~ /^[\w ]+$/;

my $algorithm = $cgi->param('algorithm');
die "Bad algorithm module" unless $algorithms{$algorithm};

print <<EOHTML;
Content-type: text/html

<html>
 <body>
  <h1>Assignments:</h1>
  <table border="1">
   <tr>
    <td><b>Player</b></td>
    <td><b>Role</b></td>
    <td><b>Amount</b></td>
   </tr>
EOHTML


my @players;
my %playerinv;
{
    my $sth = $dbh->prepare('SELECT playername FROM GameBids WHERE gamename=? GROUP BY playername');
    $sth->execute($gamename);
    while (my $data = $sth->fetchrow_hashref) {
        push @players, $data->{playername};
    }

    for (0..$#players) {
        $playerinv{$players[$_]} = $_;
    }
}

my @roles;
my %roleinv;
{
    my $sth = $dbh->prepare('SELECT rolename,count FROM GameRoles WHERE gamename=? GROUP BY rolename');
    $sth->execute($gamename);
    while (my $data = $sth->fetchrow_hashref) {
        push @roles, ($data->{rolename}) x $data->{count};
    }
    for (0..$#roles) {
        push @{$roleinv{$roles[$_]} ||= []}, $_;
    }
}

my @matrix;
for my $i (0..$#players) {
    for my $j (0..$#roles) {
        $matrix[$i][$j] = 0;
    }
}
{
    my $sth = $dbh->prepare('SELECT playername,rolename,bid FROM GameBids WHERE gamename=?');
    $sth->execute($gamename);
    while (my $data = $sth->fetchrow_hashref) {
        for (@{$roleinv{$data->{rolename}}}) {
            $matrix[$playerinv{$data->{playername}}][$_] = -$data->{bid};
        }
    }
}

my @result;
eval "require $algorithm; 1" or die "Failed to use algorithm '$algorithm'";
{
    no strict 'refs';
    &{"$algorithm\::assign"}(\@matrix, \@result);
}

for (0..$#players) {
    print <<EOHTML;
   <tr>
    <td>$players[$_]</td>
    <td>$roles[$result[$_]]</td>
    <td>@{[-$matrix[$_][$result[$_]]]}</td>
   </tr>
EOHTML
}

print <<EOHTML;
  </table>
  <form action="deletegame.pl">
   <input type="hidden" name="gamename" value="$gamename" /><br />
   <input type="submit" value="Close Game" />
  </form>
 </body>
</html>
EOHTML
print " </body>\n";
print "</html>\n";

$dbh->disconnect;
