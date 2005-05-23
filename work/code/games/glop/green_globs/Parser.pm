package Parser;

use strict;
use Parse::RecDescent;
use Regexp::Common;

my $grammar = <<'#\'GRAMMAR';
#\

{
    our %OPMAP = (
        '^' => '**',
        '+' => '+',
        '-' => '-',
        '*' => '*',
        ''  => '*',
        '/' => '/',
    );
}

eqset: equation(s /;/) /\z/
        { $item[1] }

equation: expression '=' expression
        { [ $item[1], $item[3] ] }

expression: sum

additive_operator: '+' | '-'

sum: <leftop: quotient additive_operator quotient>
        {
            if (@{$item[1]} == 1) {
                $item[1][0];
            }
            else {
                my $paren = 0;
                join ' ', map { ($paren = !$paren) ? "($_)" : $OPMAP{$_} } @{$item[1]};
            }
        }

divisive_operator: '/'

quotient: <leftop: product divisive_operator product>
        {
            if (@{$item[1]} == 1) {
                $item[1][0];
            }
            else {
                my $paren = 0;
                join ' ', map { ($paren = !$paren) ? "($_)" : $OPMAP{$_} } @{$item[1]};
            }
        }

multiplicative_operator: '*' | '' ...!/[+-]/ { $item[1] }

product: <leftop: named_op multiplicative_operator named_op>
        {
            if (@{$item[1]} == 1) {
                $item[1][0];
            }
            else {
                my $paren = 0;
                join ' ', map { ($paren = !$paren) ? "($_)" : $OPMAP{$_} } @{$item[1]};
            }
        }

named_unary: /sin|cos|tan|log|abs|sqrt|Re|Im|arg|step/

named_op: named_unary product
        { "$item[1]($item[2])" }
    |     negation

negation: '-' power 
        { "- ($item[2])" }
    |     '+' power 
    |     power
        

exponential_operator: '^'

power: term exponential_operator negation
        { "($item[1]) $OPMAP{$item[2]} ($item[3])" }
     | term

term: '(' expression ')'
        { $item[2] }
    |     named_unary exponential_operator negation '(' expression ')'
        { "$item[1]($item[5]) $OPMAP{$item[2]} ($item[3])" }
    |     named_unary '(' expression ')'
        { "$item[1]($item[3])" }
    | number
    | symbol
    | variable
    | '|' expression '|'
        { "abs($item[2])" }
    | <perl_codeblock>
        { "do $item[1]" }

number: /$Regexp::Common::RE{num}{real}/

symbol: /e|i|pi/

variable: /[a-zA-Z]/
        { "\$$item[1]" }

#'GRAMMAR

my $parser = Parse::RecDescent->new($grammar);

sub parse {
    my ($class, $text) = @_;
    $parser->eqset($text);
}

1;
