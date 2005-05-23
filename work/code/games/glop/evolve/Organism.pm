package Organism;

use strict;
use Brain;
use Field;

use Glop;
use Glop::AutoGL;

sub new {
    my ($class, $px, $py) = @_;

    bless {
        px => $px,
        py => $py,
        brain => Brain->new([
            Field->info_types * 5 + 1 + 4,  # 1 for the bias, 4 for memory
            Field->info_types * 5 + 1 + 4,
            Organism->action_types + 4,     # 4 for memory
        ]),
        divtime => 0,
        life => 100,
        age  => 0,
        memory => [ 0, 0, 0, 0 ],
    } => ref $class || $class;
}

sub position {
    my ($self) = @_;
    ($self->{px}, $self->{py});
}

sub step {
    my ($self, $field) = @_;
    my $layer1 = [ 1, @{$self->{memory}} ];
    for ([ 0, 0 ], [ -1, 0 ], [ 1, 0 ], [ 0, -1 ], [ 0, 1 ]) {
        push @$layer1, $field->info($_->[0] + $self->{px}, $_->[1] + $self->{py});
    }
    my $result = $self->{brain}->run($layer1);
    @{$self->{memory}} = splice @$result, 0, 4;
    $self->{divtime}++;
    $self->act($field, $result);

    $self->{life}-- > 0 && $self->{age}++ < 500;  # 500 days max age
}

sub action_types { 6 }

sub act {
    my ($self, $field, $actions) = @_;
    my %actions = (
        up     => $actions->[0],
        down   => $actions->[1],
        left   => $actions->[2],
        right  => $actions->[3],
        eat    => $actions->[4],
        divide => $actions->[5],
    );
    
    if ($actions{divide}) {
        if ($self->{divtime} > 125) {
            my $kid = bless {
                px => $self->{px} + int(rand 21)-10,
                py => $self->{py} + int(rand 21)-10,
                brain => $self->{brain}->clone->mutate(0.1, 0.1),
                divtime => 0,
                life => 100,
                ags  => 0,
                memory => [ 0, 0, 0, 0 ],
            };
            $field->add($kid);
            $self->{divtime} = 0;
        }
    }

    $self->{eated} = 0;
    if ($actions{eat}) {
        $self->{eated} = 1;
        if ($self->{life} < 200) {
            $self->{life} += $field->eat($self->{px}, $self->{py});
        }
    }

    $self->{py}++ if $actions{up};
    $self->{py}-- if $actions{down};
    $self->{px}++ if $actions{right};
    $self->{px}-- if $actions{left};
}

sub draw {
    my ($self) = @_;
    preserve {
        glTranslate($self->{px}, $self->{py}, 0);
        
        if ($self->{eated}) {
            glColor(0.5, 0.5, 1);
            Glop::Draw->Circle(-radius => 0.75);
        }
        
        my $int = $self->{life}/75;
        glColor(1,$int,$int);
        Glop::Draw->Circle(-radius => 0.5);
    };
}

1;
