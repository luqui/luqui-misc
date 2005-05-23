package Brain;

use strict;
use PDL;
use PDL::Matrix;
use Inline Pdlpp => <<'EOPDL';
pp_def('step',
       Pars => 'i();[o] o()',
       Code => '$o() = $i() >= 1 ? 1 : 0;',
);
EOPDL

sub new {
    my ($class, $layerns) = @_;

    my @edges;
    for my $layer (0..$#$layerns-1) {
        $edges[$layer] = mzeroes($layerns->[$layer+1], $layerns->[$layer]);
        for my $i (0..$layerns->[$layer]-1) {
            for my $j (0..$layerns->[$layer+1]-1) {
                $edges[$layer]->set($j, $i => 2*rand()**$layerns->[$layer]);
            }
        }
    }

    bless {
        edges => \@edges,
        layers => scalar @$layerns,
    } => ref $class || $class;
}

sub clone {
    my ($self) = @_;
    my @edges;
    for (@{$self->{edges}}) {
        push @edges, $_->copy;
    }
    bless {
        edges => \@edges,
        layers => $self->{layers},
    } => ref $self;
}

sub run {
    my ($self, $ainput) = @_;
    my $input = vpdl(@$ainput);
    my $layer = 0;
    my $output = $input;

    while ($layer < $self->{layers}-1) {
        ($input, $output) = ($output, undef);
        $output = ($self->{edges}[$layer] x $input)->step;
        $layer++;
    }

    [ $output->list ];
}

sub mutate {
    my ($self, $mulvar, $addvar) = @_;
    for my $layer (@{$self->{edges}}) {
        for my $i (0..$layer->dim(0)-1) {
            for my $j (0..$layer->dim(1)-1) {
                $layer->index2d($i,$j) *= 1 + (rand($mulvar) - $mulvar/2);
                $layer->index2d($i,$j) += rand($addvar) - $addvar/2;
            }
        }
    }
    $self;
}

1;
