#!/usr/bin/perl

use lib '../../lib/lib/perl5/site_perl/5.8.4';

use CGI qw{-debug};
use Sort::Naturally;
use Perl6::Interpolators;

my $cgi = CGI->new;

my $sort = $cgi->param('sort') || 'date';

my %SORTER = (
    date => sub { -M $_[0] <=> -M $_[1] },
    name => sub { ncmp(($_[0] =~ m[ ([^/]*)$ ]x)[0], 
                       ($_[1] =~ m[ ([^/]*)$ ]x)[0]) },
    dir  => sub { ncmp($a, $b) },
);

sub getfiles(;&$) {
    my ($pred, $name) = @_;
    $name ||= '.';
    $name .= '/' unless $name =~ m#/$#;
    $pred ||= sub { 1 };

    my @mine;
    my @child;

    opendir my $dir, $name or die "Couldn't open $name for reading: $!";
    for (readdir $dir) {
        next if /^\./ || /~$/;
        my $file = "$name$_";
        if (-d $file) {
            push @child, $file;
        }
        push @mine, $file if $pred->($file); 
    }
    
    my $sorter = $sort =~ /^-(.*)$/ ? 
            sub { $SORTER{$1}->(reverse @_) } : 
            sub { $SORTER{$sort}->(@_) };
    return sort { $sorter->($a,$b) } @mine, 
        map { getfiles($pred, $_) } @child;
}

sub pred {
    local $_ = shift;
    not -d and /\.(?:mid|mp3|pdf)$/i
}

print <<EOHEAD;
Content-type: text/html

<html>
 <head>
  <link rel="stylesheet" href="style.css">
  <title>Luke Palmer's compositions</title>
 </head>
 <body>
  <center>  <!-- It's dumb that CSS can't even center things! -->
  <h1>Works by Luke Palmer</h1>
  <table>
   <thead>
    <tr>
     <td><a class="header" 
            href="?sort=$( $sort eq 'date' ? '-date' : 'date' )">
          Date </a> </td>
     <td><a class="header"
            href="?sort=$( $sort eq 'dir' ? '-dir' : 'dir' )">
          Category </a> </td>
     <td><a class="header"
            href="?sort=$( $sort eq 'name' ? '-name' : 'name' )">
          Name </a> </td>
    </tr>
   </thead>
   <tbody>
EOHEAD

for (getfiles \&pred) {
    my $mtime = (stat)[9];
    my (undef, undef, undef, $mday, $mon, $year) = localtime $mtime;
    
    print <<EODATA;
    <tr>
     <td>$( $year+1900 )-$( $mon+1 )-$mday</td>
     <td>@( m[\./(.*/)] )</td>
     <td><a href="$_">@( m[([^/]*)$] )</a></td>
    </tr>
EODATA
}

print <<EOTAIL;
   </tbody>
  </table>
    <!-- Creative Commons License -->
    <a rel="license" href="http://creativecommons.org/licenses/by-nc-sa/1.0/"><img alt="Creative Commons License" border="0" src="http://creativecommons.org/images/public/somerights.gif" /></a><br />
    This work is licensed under a <a rel="license" href="http://creativecommons.org/licenses/by-nc-sa/1.0/">Creative Commons License</a>.
    <!-- /Creative Commons License -->


    <!--

    <rdf:RDF xmlns="http://web.resource.org/cc/"
        xmlns:dc="http://purl.org/dc/elements/1.1/"
        xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">
    <Work rdf:about="">
       <dc:type rdf:resource="http://purl.org/dc/dcmitype/Sound" />
       <license rdf:resource="http://creativecommons.org/licenses/by-nc-sa/1.0/" />
    </Work>

    <License rdf:about="http://creativecommons.org/licenses/by-nc-sa/1.0/">
       <permits rdf:resource="http://web.resource.org/cc/Reproduction" />
       <permits rdf:resource="http://web.resource.org/cc/Distribution" />
       <requires rdf:resource="http://web.resource.org/cc/Notice" />
       <requires rdf:resource="http://web.resource.org/cc/Attribution" />
       <prohibits rdf:resource="http://web.resource.org/cc/CommercialUse" />
       <permits rdf:resource="http://web.resource.org/cc/DerivativeWorks" />
       <requires rdf:resource="http://web.resource.org/cc/ShareAlike" />
    </License>

    </rdf:RDF>

    -->
  </center>
 </body>
</html>
EOTAIL
