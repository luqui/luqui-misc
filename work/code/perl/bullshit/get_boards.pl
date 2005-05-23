#!/usr/bin/perl

my $card = qr/[2-9TJQKA][cdhs]/;

my @chand;
while (<>) {
    if (/^\*\*\s*Dealing\s+Flop\s*\*\*\s*\[\s*($card),\s*($card),\s*($card)\s*\]/) {
        print "@chand\n" if @chand;
        @chand = ($1, $2, $3);
    }
    elsif (/^\*\*\s*Dealing\s+Turn\s*\*\*\s*\[\s*($card)\s*\]$/) {
        push @chand, $1;
    }
    elsif (/^\*\*\s*Dealing\s+River\s*\*\*\s*\[\s*($card)\s*\]$/) {
        push @chand, $1;
    }
}

print "@chand\n" if @chand;
