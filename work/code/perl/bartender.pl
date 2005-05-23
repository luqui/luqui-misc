#!/usr/bin/perl

my @glasses = map { int rand 2 } 0..3;

sub print_table {
    my %m = (0 => 'o', 1 => '*');
    print "4 $m{0+$glasses[3]} --- $m{0+$glasses[2]} 3\n";
    print "  |     |\n";
    print "1 $m{0+$glasses[0]} --- $m{0+$glasses[1]} 2\n";
}

sub user_input {
    print "Rotate clockwise how many times? ";
    chomp(my $times = <STDIN>);
    goto &user_input unless $times =~ /^\d+$/;
    push @glasses, shift @glasses for 1..$times;
}

sub check_win {
    if ($glasses[0] == $glasses[1] && 
        $glasses[1] == $glasses[2] &&
        $glasses[2] == $glasses[3]) {
            print "===\n";
            print_table();
            print "You lose!\n";
            exit;
    }
}

sub next_move {
    my ($a, $b) = @_;
    check_win();
    print "===\n";
    print_table();
    print "I'm going to check @{[$a+1]} and @{[$b+1]} next\n";
    user_input();
    print_table();
}

sub algorithm {
    next_move(0, 1);
    @glasses[0,1] = (0,0);
    
    next_move(0, 2);
    @glasses[0,2] = (0,0);
    
    next_move(0,1);
    if ($glasses[0]) {
        $glasses[0] = 0;
    }
    elsif ($glasses[1]) {
        $glasses[1] = 0;
    }
    else {
        $glasses[0] = 1;
    }

    next_move(0,1);
    $glasses[0] = !$glasses[0];
    $glasses[1] = !$glasses[1];

    next_move(0,2);
    $glasses[0] = !$glasses[0];
    $glasses[2] = !$glasses[2];

    check_win();

    print "I guess you win... (how did that happen?)\n";
    exit;
}

algorithm();
