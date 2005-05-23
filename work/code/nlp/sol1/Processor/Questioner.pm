package Processor::Questioner;

use strict;

use Carp;
use Term::ReadLine;
use Switch 'Perl6';

my $term = Term::ReadLine->new('preproc');

sub new {
    my ($class, $data) = @_;
    $data = do $data or croak $@ if $data and not ref $data;

    bless {
        data => $data,
    } => ref $class || $class;
}

sub lookup {
    my ($self, $datid, %args) = @_;

    if (my $answers = $self->{data}{$datid}) {
        for my $answer (@$answers) {
            my $possible;
            if ($answer->{text}) {
                if (lc $answer->{text} eq lc $args{data}) {  # XXX: should this really be case insensitive?
                    $possible = $answer->{answer};
                }
            }

            elsif ($answer->{regex}) {
                if ($args{data} =~ /$answer->{regex}/) {
                    $possible = $answer->{answer};
                }
            }

            elsif ($answer->{code}) {
                if (my $res = $answer->{code}->($datid, $args{data}, $args{answers})) {
                    $possible = $res;
                }
            }

            if ($possible) {
                if ($args{answers}{$possible}) {
                    return $possible;
                }
                else {
                    warn "Answer '$possible' not valid for question id $datid\n";
                }
            }
        }
    }
    return;
}

sub ask_user {
    my ($self, $datid, %args) = @_;

    $args{question} ||= "$args{id} \"$args{data}\"?";
    print "$args{question}\n";
    for (sort keys %{$args{answers}}) {
        print "    $_: $args{answers}{$_}\n";
    }

    my $response;
    while (1) {
        $response = $term->readline('? ');
        last if $args{answers}{$response};
        print "Invalid Response.\n";
    }

    push @{$self->{data}{$datid}}, {
        text => $args{data},
        answer => $response,
    };

    $response;
}

sub ask {
    my ($self, %args) = @_;
    $args{module}  ||= caller;
    $args{id}      ||= 'none';
    $args{data}    || croak "Must give a data segment";
    $args{answers} ||= {
        keep => "Keep",
        skip => "Skip",
    };
    my $datid = "$args{module}/$args{id}";

    $self->lookup($datid, %args) || $self->ask_user($datid, %args);
}
