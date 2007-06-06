#!/usr/bin/perl

use strict;
use DBI ();

my $dbh = DBI->connect('DBI:mysql:werepoker', 'fibonaci', 'sre-piz',
                        { RaiseError => 1, AutoCommit => 0 })
            or die "Couldn't connect to database: " . DBI->errstr;

print <<EOHTML;
Content-type: text/html

<html>
 <head>
  <title>Join Werepoker Game</title>
 </head>
 <body>
  <h1>Join Werepoker Game</h1>
  <form method="post" action="joingame.pl">
   <select name="gamename">
EOHTML

my $sth = $dbh->prepare('SELECT gamename FROM GameRoles GROUP BY gamename');
$sth->execute;
while (my $data = $sth->fetchrow_hashref) {
    print "<option value=\"$data->{gamename}\">$data->{gamename}</option>\n";
}

print <<EOHTML;
   </select>
   <input type="submit" />
  </form>
 </head>
</html>
EOHTML

$dbh->disconnect;
