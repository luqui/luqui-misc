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
EOHTML

my $status = eval {
    $dbh->prepare('DELETE FROM GameRoles WHERE gamename=?')->execute($gamename);
    $dbh->prepare('DELETE FROM GameBids WHERE gamename=?')->execute($gamename);
    1;
};

if ($status) {
    $dbh->commit;
    print "Game closed.\n";
}
else {
    $dbh->rollback;
    print "Game deletion failed.  Wtf?\n";
}

print " </body>\n";
print "</html>\n";

$dbh->disconnect;
