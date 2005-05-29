package Glop::TransientQueue;

use Want qw{ howmany };
use Carp;

sub new {
    my ($class) = @_;
    bless [ ] => ref $class || $class;
}

sub run {
    my $q = $_[0];
    while (@$q) {
        if ($q->[0]->()) {
            last;
        }
        else {
            shift @$q;
        }
    }
}

sub push {
    push @{$_[0]}, @_[1..$#_];
}

sub unshift {
    unshift @{$_[0]}, @_[1..$#_];
}

sub size {
    scalar @{$_[0]};
}

sub fork {
    # This function itself need not be fast; but the black magic it performs
    # makes the rest of the class fast.  Warning: in the presence of a DESTROY
    # method, this class will have to be refactored.
    my ($self, $count) = @_;
    my $oldself = bless [ @$self ] => ref $self;

    my $howmany = $count || howmany;
    unless ($howmany) {
        if (defined $howmany) {
            croak "Must split into at least one queue";
        }
        else {
            croak "Cannot determine into how many queues to split"
        }
    }

    @$self = (
        $oldself,
        map { Glop::TransientQueue->new } 0..$howmany-1
    );
    bless $self => Glop::TransientQueue::Parallel;
    (@$self);
}

BEGIN {
    *enqueue = \&push;
    *preempt = \&unshift;
}

package Glop::TransientQueue::Parallel;

use Carp;

sub new {
    croak "Can't create a Glop::TransientQueue::Parallel directly; use ".
          "Glop::TransientQueue::fork instead";
}

sub push {
    croak "Can't push onto a parallel queue; use its child queues instead";
}

sub unshift {
    croak "Can't preempt a parallel queue; use its child queues instead";
}

sub run {
    for (@{$_[0]}) {
        $_->run;
    }
}

sub size {
    # this really isn't a meaningful operation
    # but we return the max size of any of the queues
    my $sz = 0;
    for (@{$_[0]}) {
        $sz = $_->size if $_->size > $sz;
    }
    $sz;
}

sub children {
    @{$_[0]};
}

BEGIN {
    *fork = \&Glop::TransientQueue::fork;
    *enqueue = \&push;
    *preempt = \&unshift;
}

1;
