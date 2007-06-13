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

my $roles = $cgi->param('roles');
die "Malformed roles" unless $roles =~ /^[\w, \*]+$/;

my @roles;
for my $role (split /\s*,\s*/, $roles) {
    if ($role =~ /^(\w+)\s*\*\s*(\d+)$/) {
        push @roles, { role => $1, count => $2 };
    }
    elsif ($role =~ /^(\w+)$/) {
        push @roles, { role => $1, count => 1 };
    }
    else {
        die "Malformed role: '$role'";
    }
}

my $status = eval {
    my $query = $dbh->prepare('INSERT INTO GameRoles VALUES (?,?,?)');
    for (@roles) {
        $query->execute($gamename, $_->{role}, $_->{count});
    }
    1;
};

if ($status) {
    $dbh->commit;
    print "Content-type: text/html\n\n";
    print <<EOHTML;
    <html>
     <body>
      <h1>$gamename</h1>
      <p>Click below when bidding has finished.</p>
      <form method="get" action="adjudicate.pl">
       <input type="hidden" name="gamename" value="$gamename" />
       Resolution Algorithm:
       <select name="algorithm">
        <option value="Algorithm::Munkres">Largest pot</option>
        <option value="BidPicker">Highest bid</option>
       </select>
       <br />
       <input type="submit" value="Adjudicate" />
      </form>
     </body>
    </html>
EOHTML
}
else {
    $dbh->rollback;
    print "Content-type: text/plain\n\n";
    print "Creating game failed.  Sorry.\n";
}

$dbh->disconnect;
