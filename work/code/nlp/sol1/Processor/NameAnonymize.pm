package Processor::NameAnonymize;

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
        ask => $questioner,
        log => $fh,
        list => Processor::NameAnonymize::NameList->new,
    } => ref $class || $class;
}

sub _anonymize {
    my ($self, $docid, $text, $pre, $first, $middle, $last, $post) = @_;
    my (%data, $gender, $doc);

    if    ($pre =~ /mr?s/i) { $gender = 'female' }
    elsif ($pre =~ /mr/i)   { $gender = 'male' }

    if ($post =~ /m\.?d/i)  { $doc = 'yes' }

    my %opts = (
        gender => $gender,
        doctor => $doc,
        first  => $first,
        middle => $middle,
        last   => $last,
    );
    for (keys %opts) {
        $opts{$_} = uc $opts{$_};
        delete $opts{$_} if $opts{$_} eq '';
    }
    
    my $name = $self->{list}->get(%opts);
    
    my $id = $name->{id};

    $text =~ s/\s+/ /g;  # squash whitespace
    print { $self->{log} } 
        "$docid` \"$text\" === $id { " . 
            join(', ', 
                map { "$_ => $name->{$_}" } sort keys %$name,
            ) . " }\n"; 
    $id; 
}

my $ws    = qr/[ ]*\n | [ ]/x;
my $hspace = qr/[ \t]*/;
my $patientno = qr/[A-Z]{2}\d{4}/x;

my $first = qr/
    (?: [A-Z][a-z]+ | [A-Z]{2,} )
/x;
my $last  = qr/
    (?:M[cC]|O')? 
    (?: [A-Z][a-z]+ (?:-[A-Z][a-z]+)*
      | [A-Z]{2,}   (?:-[A-Z]{2,})*
    )
/x;

my $name  = qr/
    (?: (D[Rr]\.|M[Rr]\.|M[Rr]?[Ss]\.) $ws )?
    (?: (?: [A-Z]\.? $ws )? ($first) $ws )?
    (?: ([A-Z])\.? $ws )?
    ($last)
    (?:, $ws (M\.?D\.?))?
/x;

sub process {
    my ($self, $docid, $text) = @_;
    local $_ = $text;

    my ($prehead, $head);
    s/\A $hspace $patientno $hspace \n $hspace \n//x and $prehead = $&;

    s/\A .*? \n//x and $head = $&;
    $head =~ s[ ($last), $hspace ($first) $hspace ([A-Z]\.)? ]{
        $self->_anonymize($docid, $&, undef, $2, $3, $1, undef)
    }gsex;
    
    s[ $name ]
     { 
         $1 || $2 && $3 || $2 && $5
            ? $self->_anonymize($docid, $&, $1, $2, $3, $4, $5)
            : $&
     }gsex;
    
    $prehead . $head . $_;
}

package Processor::NameAnonymize::NameList;

sub new {
    my ($class) = @_;
    bless { 
        names => [ ],
        curid => '000000',
    } => ref $class || $class;
}

sub create {
    my ($self, %data) = @_;
    my $new = \%data;
    $new->{id} = 'N' . $self->{curid}++;
    push @{$self->{names}}, $new;
    $new;
}

sub merge {
    my ($self, $name, %data) = @_;
    $name->{$_} = $data{$_} for keys %data;
    $name;
}

sub get {
    my ($self, %data) = @_;
    
    NAME:
    for my $name (@{$self->{names}}) {
        for my $key (keys %data) {
            if (exists $name->{$key}) {
                next NAME unless $name->{$key} eq $data{$key};
            }
        }
        return $self->merge($name, %data);
    }
    return $self->create(%data);
}

1;
