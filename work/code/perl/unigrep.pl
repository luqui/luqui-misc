#!/usr/bin/perl

binmode STDOUT, ":utf8";
my $pat = "@ARGV";

for (split /^/, do 'unicore/Name.pl') {
    if (/$pat/oi) {
        print chr hex, "\t", $_;
    }
}
        
    
