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

my $playername = $cgi->param('playername');
die "Malformed player name" unless $playername =~ /^[\w ]+$/;

my %bids;
for my $param ($cgi->param) {
    if ($param =~ /^bid-(\w+)$/) {
        $bids{$1} = int($cgi->param($param));
        if ($bids{$1} < 0) { $bids{$1} = 0; }
    }
}

my $status = eval {
    # Delete the old bids so you can resubmit with the same name if you like.
    $dbh->prepare('DELETE FROM GameBids WHERE gamename=? AND playername=?')
        ->execute($gamename, $playername);
        
    my $sth = $dbh->prepare('INSERT INTO GameBids VALUES (?,?,?,?)');

    # Insert new bids into the database.
    for (keys %bids) {
        $sth->execute($gamename, $playername, $_, $bids{$_});
    }
    1;
};

if ($status) {
    $dbh->commit;
    print "Content-type: text/html\n\n";
    print <<EOHTML;
    <html>
     <body>
      <h1>Got it!</h1>
      <p>Submit to add another player.</p>
      <form method="get" action="joingame.pl">
       <input type="hidden" name="gamename" value="$gamename" />
       <input type="submit" />
      </form>
     </body>
    </html>
EOHTML
}
else {
    $dbh->rollback;
    print "Content-type: text/plain\n\n";
    print "Bidding failed.  Sorry.\n";
}

$dbh->disconnect;
