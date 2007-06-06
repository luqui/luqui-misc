#!/usr/bin/perl

use strict;
use CGI ();
use DBI ();
use Algorithm::Munkres ();

my $dbh = DBI->connect('DBI:mysql:werepoker', 'fibonaci', 'sre-piz',
                        { RaiseError => 1, AutoCommit => 0 })
            or die "Couldn't connect to database: " . DBI->errstr;

my $cgi = CGI->new;

my $gamename = $cgi->param('gamename');
die "Malformed game name" unless $gamename =~ /^[\w ]+$/;

print <<EOHTML;
Content-type: text/html

<html>
 <body>
  <h1>Assignments:</h1>
  <table>
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
    my $sth = $dbh->prepare('SELECT rolename FROM GameRoles WHERE gamename=? GROUP BY rolename');
    $sth->execute($gamename);
    while (my $data = $sth->fetchrow_hashref) {
        push @roles, $data->{rolename};
    }
    for (0..$#roles) {
        $roleinv{$players[$_]} = $_;
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
        $matrix[$playerinv{$data->{playername}}][$roleinv{$data->{rolename}}] = -$data->{bid};
    }
}

my @result;
Algorithm::Munkres::assign(\@matrix, \@result);

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
EOHTML



my $status = eval {
    $dbh->prepare('DELETE FROM GameRoles WHERE gamename=?')->execute($gamename);
    $dbh->prepare('DELETE FROM GameBids WHERE gamename=?')->execute($gamename);
    1;
};

if ($status) {
    $dbh->commit;
    print "Game deleted.\n";
}
else {
    $dbh->rollback;
    print "Game deletion failed.  Wtf?\n";
}

print " </body>\n";
print "</html>\n";

$dbh->disconnect;
