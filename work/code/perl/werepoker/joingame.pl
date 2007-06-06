#!/usr/bin/perl

use strict;
use CGI ();
use DBI ();

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
  <h1>Bid on Roles</h1>
  <form method="post" action="bid.pl">
   <input type="hidden" name="gamename" value="$gamename" />
   <table border="0">
    <tr>
     <td>Player Name:</td>
     <td><input type="text" name="playername" /></td>
    </tr>
EOHTML

my @roles;
my $sth = $dbh->prepare('SELECT rolename, count FROM GameRoles WHERE gamename=? GROUP BY rolename');
$sth->execute($gamename);
while (my $data = $sth->fetchrow_hashref) {
    print <<EOHTML;
    <tr>
     <td>Bid on $data->{rolename} ($data->{count})</td>
     <td><input type="text" name="bid-$data->{rolename}" /></td>
    </tr>
EOHTML
}

print <<EOHTML;
   </tr>
  </table>
  <input type="submit" />
 </body>
</html>
EOHTML

$dbh->disconnect;
