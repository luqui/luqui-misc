#!/usr/bin/perl

use Parse::RecDescent;

my $grammar = <<'EOG';

{
    sub reduce {
        my ($op, @s) = @_;
        if ($op->{value} eq 'u-') {
            push @s, -pop @s;
        }
        elsif ($op->{value} eq '+') {
            push @s, pop(@s) + pop(@s);
        }
        elsif ($op->{value} eq '-') {
            push @s, -pop(@s) + pop(@s);
        }
        elsif ($op->{value} eq '*') {
            push @s, pop(@s) * pop(@s);
        }
        elsif ($op->{value} eq '/') {
            push @s, 1 / pop(@s) * pop(@s);
        }
        elsif ($op->{value} eq '^') {
            my $exp = pop @s;
            push @s, pop(@s) ** $exp;
        }
        @s;
    }

    sub do_reduce_q {
        my ($op, $opstack) = @_;
        
        return unless @$opstack;

        $op->{prec} <  $opstack->[-1]{prec}
        || $op->{prec} == $opstack->[-1]{prec} 
            && $op->{assoc} eq 'left';
    }

    sub status {
        my ($tok, $termstack, $opstack) = @_;
       
        my $tokstr  = ref $tok ? $tok->{value} : $tok;
        my $termstr = join(' ', reverse @$termstack);
        my $opstr   = join(' ', reverse map { $_->{value} } @$opstack);

        printf STDERR "%3s | %24s | %24s |\n", $tokstr, $termstr, $opstr;
        1;
    }
}

term: /- | \d* \. \d* | \d+/x {
    if ($item[1] eq '-') {
        { 
            type => 'prefix',
            prec => 1,
            assoc => 'left',
            value => 'u-',
        }
    }
    else {
        if ($item[1] eq '.') { 0 }
        else { $item[1] }
    }
}

operator: /\+ | - | \* | \/ | \^/x {
    {
        type => 'infix',
        prec => ($item[1] =~ /[+-]/ ? 1 : 
                 $item[1] =~ /\// ? 2 : 
                 $item[1] =~ /\*/ ? 3 :
                 4),
        assoc => ($item[1] =~ /\^/ ? 'right' : 'left'),
        value => $item[1],
    }
}
        | {
    {
        type => 'EOF',
        prec => 0,
        assoc => 'left',
        value => 'EOF',
    }
}

expression: opex /\z/ { $item[1] }

opex: opex_term[ opstack => [ ], termstack => [ ] ]

opex_term: term { status($item[1], $arg{termstack}, $arg{opstack}) }
           opex_term_fork[ term => $item[1], 
                           opstack => $arg{opstack}, 
                           termstack => $arg{termstack} ]

opex_term_fork: <reject: ! ref $arg{term}>  # prefix
                opex_term[ opstack => [ @{$arg{opstack}}, $arg{term} ],
                           termstack => $arg{termstack} ]
              | # term
                opex_op[ opstack => $arg{opstack},
                         termstack => [ @{$arg{termstack}}, $arg{term} ] ]

opex_op: operator 
         opex_op_reduce[ op => $item[1],
                         opstack => $arg{opstack},
                         termstack => $arg{termstack} ]

opex_op_reduce: { status($arg{op}, $arg{termstack}, $arg{opstack}) } <reject> 
              | <reject: !do_reduce_q($arg{op}, $arg{opstack})>
                opex_op_reduce[ op => $arg{op},
                                opstack => [ @{$arg{opstack}}[0..$#{$arg{opstack}}-1] ],
                                termstack => [ reduce($arg{opstack}[-1], @{$arg{termstack}}) ] ]
              | opex_op_fork[ op => $arg{op},
                              opstack => $arg{opstack},
                              termstack => $arg{termstack} ]

opex_op_fork: <reject: $arg{op}{type} ne 'EOF'>
              { $arg{termstack}[-1] }
            | <reject: $arg{op}{type} ne 'postfix'>
              opex_op[ opstack => $arg{opstack},
                       termstack => [ reduce($arg{op}, @{$arg{termstack}}) ] ]
            | <reject: $arg{op}{type} ne 'infix'>
              opex_term[ opstack => [ @{$arg{opstack}}, $arg{op} ],
                       termstack => $arg{termstack} ]

EOG

my $parser = Parse::RecDescent->new($grammar);
my $result = $parser->expression(scalar <>);
print "\nRESULT = $result\n";
