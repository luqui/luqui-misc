package Processor::PlaceAnonymize;

use strict;

use Carp;

sub new { 
    my ($class, $logfile, $questioner) = @_;
    my $fh;
    unless (ref $logfile) {
        open $fh, '>', $logfile or croak "Couldn't open $logfile for writing: $!";
    }
    else {
        $fh = $logfile;
    }
    bless {
        ask    => $questioner,
        log    => $fh,
        places => [ ],
        curid  => '000000',
        ids    => { },
    } => ref $class || $class;
}

my $ws        = qr/[ ]* \n | [ ]/x;
my $proper    = qr/[A-Z][a-z][A-Za-z]*/x;
my $particle  = qr/and | for | in/xi;
my $word      = qr/$proper | $particle/x;
my $place     = qr/
    (?: $word $ws )* 
    (?: Center | University ) 
    (?: $ws $particle (?: $ws $word )+ )?
/x;

sub _anonymize {
    my ($self, $docid, $cap) = @_;

    my ($pre, $post);
    my $anon = $cap;
    # XXX: Bugging the user with no way to tell it not to
    if ($cap =~ /\n/) {
        (my $newcap = $cap) =~ s/\n/\\n/g;

        my $inp = $self->{ask}->ask(
            id       => 'linebreak',
            data     => $newcap,
            question => "The string \"$newcap\" has a line break (\\n) in it ($docid)",
            answers  => {
                left  => "Just to the left is a place name",
                right => "Just to the right is a place name",
                whole => "The whole thing is a place name",
                skip  => "Skip this case",
            },
        );

        if ($inp eq 'whole') {
            $anon = $cap;
        }
        elsif ($inp eq 'left') {
            ($anon, $post) = $cap =~ /^ (.*) (\n .*) $/x;
        }
        elsif ($inp eq 'right') {
            ($pre, $anon) = $cap =~ /^ (.* \n) (.*) $/x;
        }
        elsif ($inp eq 'skip') {
            return $cap;
        }
    }

    $anon =~ s/\s+/ /g;
    my $id = $self->{ids}{uc $anon} ||= 'P' . $self->{curid}++;
    print { $self->{log} } "$docid` $anon => $id\n";
    $id;
}

sub process {
    my ($self, $docid, $text) = @_;
    local $_ = $text;

    s/$place/ $self->_anonymize($docid, $&) /ge;
    $_;
}
