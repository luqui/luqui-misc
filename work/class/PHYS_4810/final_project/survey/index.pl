#!/usr/bin/perl

use strict;
use CGI ();
use Algorithm::Numerical::Shuffle qw<shuffle>;
use Data::Dumper;

my $ALMOST = "Almost correct.  The grader said that on the final she would " .
             "count off for incorrect cases and other such pedantic things, " .
             "so make sure you are precise about your answer.";

my %problems = (
#######################
    'con-shortcircuit' => {
        text => <<'EOT',
   If the sub-expression on the left side of an <tt>||</tt> operator is true,
   the expression on the right side will not be checked.<br />
   <b>True</b> <input type="radio" name="con-shortcircuit" value="true" />
   <b>False</b> <input type="radio" name="con-shortcircuit" value="false" />
EOT
        evaluate => sub {
            my ($ans) = @_;
            return $ans eq 'true' ? 'Correct' : 'Incorrect';
        },
    },
    
######################
    'app-shortcircuit' => {
        text => <<'EOT',
   <pre>
    int main() 
    {
        int x = 0, y = 9;
        if (y &gt; 5 || x++ == 5) 
        {
            cout &lt;&lt; "Good ";
        }
        else
        {
            cout &lt;&lt; "Bad ";
        }

        cout &lt;&lt; x &lt;&lt; y;
        return 0;
    }
   </pre>
   What is the output of running this program (write "error" followed by a 
   reason if there is a compile error)? <br/>
   <input type="text" name="app-shortcircuit" size="60"/>
EOT
        evaluate => sub {
            my ($ans) = @_;
            my $CORRECT = "The correct answer is <tt>Good 09</tt>.";
            return "Correct" if $ans eq 'Good 09';
            return $ALMOST . " $CORRECT" if $ans =~ /^good\s*0\s*9$/i;
            if ($ans =~ /^good\s*1\s*9$/i) {
                return <<'EOT';
    Incorrect.  Remember that if the left side of an || statement is
    true, then the right side is not evaluated.  In this case, y &gt;
    5 is true, so the x++ part is not evaluated and x is not 
    incremented.  This is because X || Y is true if either X is true
    or Y is true; if you know X is true, then there is no need to check
    Y, you already know that X || Y is true.  && also does this, but
    it stops checking if the left argument is <i>false</i>.
EOT
            }
            if ($ans =~ /^good\s*9\s*0$/) {
                return "Pretty close.  Looks like you just transposed " .
                       "the digits.  The program outputs x first, then " .
                       "y  (this is an error I made when I tried the " .
                       "problem <tt>:-)</tt>.";
            }
            return "Incorrect. $CORRECT";
        },
    },

######################
    'con-switch_default' => {
        text => <<'EOT',
   The code following the <input type="text" name="con-switch_default" size="8" /> 
   case is executed if none of the other cases are matched in a 
   <tt>switch</tt> statement.
EOT
        evaluate => sub {
            my ($ans) = @_;
            my $CORRECT = "The correct answer is <tt>default</tt>.";
            return "Correct" if $ans eq 'default';
            return "$ALMOST $CORRECT" if $ans =~ /\bdefault\b/i;
            return "Incorrect. $CORRECT";
        },
    },

######################
    'app-switch' => {
        text => <<'EOT',
   The following program should read a number from the user and print
   the number in English.  It only knows how to do the numbers 1-3, and
   if given any other number it should report "I don't know.".  Fill
   in the blanks.
   <pre>
    int main()
    {
        int num;
        cout &lt;&lt; "Please enter a number: ";
        cin &gt;&gt; num;
        switch (num) {
            <input type="text" name="app-switch:case1" size="8" />
                cout &lt;&lt; "One";
                break;
            <input type="text" name="app-switch:case2" size="8" />
                cout &lt;&lt; "Two";
                break;
            <input type="text" name="app-switch:case3" size="8" />
                cout &lt;&lt; "Three";
                break;
            <input type="text" name="app-switch:default" size="8" />
                cout &lt;&lt; "I don't know.";
                break;
        }
        return 0;
    }
   </pre>
EOT
        evaluate => sub {
            my ($ans) = @_;
            my $ramble = 0;
            my %reply;
            @reply{qw<case1 case2 case3>} = map {
                my $CORRECT = "The correct answer is <tt>case $_:</tt> (including the colon).";
                if ($ans->{"case$_"} =~ /^case\s+$_\s*:$/) {
                    'Correct'
                }
                elsif ($ans->{"case$_"} =~ /^case\s+$_\*:?$/i) {
                    unless ($ramble++) {
                        "$ALMOST $CORRECT";
                    }
                    else {
                        "Almost (see above). $CORRECT";
                    }
                }
                else {
                    "Incorrect. $CORRECT";
                }
            } 1..3;

            my $CORRECT = "The correct answer is <tt>default:</tt> (including the colon).";
            if ($ans->{"default"} =~ /^default\s*:$/) {
                $reply{'default'} = 'Correct';
            }
            elsif ($ans->{"default"} =~ /^default\s*:?$/i) {
                unless ($ramble++) {
                    $reply{'default'} = "$ALMOST $CORRECT";
                }
                else {
                    $reply{'default'} = "Almost (see above). $CORRECT";
                }
            }
            else {
                $reply{'default'} = "Incorrect. $CORRECT";
            }

            if (!grep { $_ ne 'Correct' } @reply{qw<case1 case2 case3 default>}) {
                return 'Correct';
            }
            else {
                return join "<br/>\n", map { "<b>$ans->{$_}</b> $reply{$_}" } qw<case1 case2 case3 default>;
            }
        },   
    },

######################
    'con-break' => {
        text => <<'EOT',
   The _____ statement causes a loop to terminate early.
   <ul>
    <li><input type="radio" name="con-break" value="terminate" /><tt>terminate</tt></li>
    <li><input type="radio" name="con-break" value="stop" /><tt>stop</tt></li>
    <li><input type="radio" name="con-break" value="break" /><tt>break</tt></li>
    <li><input type="radio" name="con-break" value="quit" /><tt>quit</tt></li>
    <li><input type="radio" name="con-break" value="none" />None of the above.</li>
   </ul>
EOT
        evaluate => sub {
            my ($ans) = @_;
            if ($ans eq 'break') {
                return 'Correct';
            }
            else {
                return 'Incorrect. The correct answer is <tt>break</tt>.';
            }
        },
    },

#####################
    'app-break' => {
        text => <<'EOT',
   <pre>
    int main()
    {
        int x = 1;
        while (x &gt; 0) {
            cout &lt;&lt; x &lt;&lt; " ";
            if (x &gt; 10)
            {
                break;
            }
            x = x * 2;
        }
        return 0;
    }
   </pre>
    What is the output of running this program (write "error" followed by a 
    reason if there is a compile error, and write "infinite" if it is an
    infinite loop)? <br/>
    <input type="text" name="app-break" size="60"/>
EOT
        evaluate => sub {
            my ($ans) = @_;
            my $CORRECT = 'The correct answer is <tt>1 2 4 8 16</tt>.';
            if ($ans eq '1 2 4 8 16') {
                return 'Correct';
            }
            if ($ans =~ /^1\s*2\s*4\s*8\s*16$/) {
                return "$ALMOST $CORRECT";
            }
            if ($ans =~ /^1\s*2\s*4\s*8$/) {
                return "Pretty close, but no cigar.  Does the value of <tt>x</tt> " .
                       "get output before or after the program checks to see if it's " .
                       "greater than 10? $CORRECT";
            }
            if ($ans =~ /^2\s*4\s*8(?:\s*16)?$/) {
                return "Pretty close, but no cigar.  Trace through the program as " .
                       "the computer would, line by line.  What is the first thing " .
                       "that is output? $CORRECT";
            }
            if ($ans =~ /infinite/i) {
                return "It's not an infinite loop.  When x gets larger than 10 " .
                       "(namely, 16), the if condition will succeed and then the " .
                       "<tt>break</tt> statement will be executed.  When that " .
                       "happens, the program skips to the end of the loop body " .
                       "and then ends the program with <tt>return 0</tt>. $CORRECT";
            }
            return "Incorrect. $CORRECT";
        },
    },

#######################
    'con-pretest' => {
        text => <<'EOT',
   A <tt>for</tt> loop is considered a _____ loop.
   <ul>
    <li><input type="radio" name="con-pretest" value="infinite" />infinite</li>
    <li><input type="radio" name="con-pretest" value="pre-test" />pre-test</li>
    <li><input type="radio" name="con-pretest" value="post-test" />post-test</li>
    <li><input type="radio" name="con-pretest" value="sentinel-controlled" />sentinel-controlled</li>
    <li><input type="radio" name="con-pretest" value="none" />None of the above.</li>
   </ul>
EOT
        evaluate => sub {
            my ($ans) = @_;
            if ($ans eq 'pre-test') {
                return 'Correct';
            }
            else {
                return 'Incorrect.  The correct answer is "pre-test".';
            }
        },
    },

######################
    
    'app-pretest' => {
        text => <<'EOT',
   <pre>
    int main()
    {
        int x = 0;
        for (int i = 5; i &lt; 0; i++) {
            x = x + 1;
        }
        cout &lt;&lt; x;
        return 0;
    }
   </pre>
   What is the output of running this program (write "error" followed by a 
   reason if there is a compile error, and write "infinite" if it is an
   infinite loop)? <br/>
   <input type="text" name="app-pretest" size="60"/>
EOT
        evaluate => sub {
            my ($ans) = @_;
            if ($ans eq '0') {
                return "Correct";
            }
            if ($ans eq '1') {
                return 'Incorrect.  i starts at 5, which is already not less than ' .
                       'zero.  So the for loop\'s condition fails, and the body is ' .
                       'just skipped over until the cout.  This is because <tt>for</tt> ' .
                       'is a "pre-test" loop.';
            }
            if ($ans =~ /infinite/i) {
                return 'Incorrect.  Quite the opposite, really.  i starts at 5, which ' .
                       'is already not less than zero, so the loop body is never ' .
                       'exectued and the program skips to the cout.';
            }
        },
    },
    
#######################
    'con-equality' => {
        text => <<'EOT',
   The _____ operator is used in C++ to represent equality.
   <ul>
    <li><input type="radio" name="con-equality" value="=" /><tt>=</tt></li>
    <li><input type="radio" name="con-equality" value="&lt;&gt;" /><tt>&lt;&gt;</tt></li>
    <li><input type="radio" name="con-equality" value="==" /><tt>==</tt></li>
    <li><input type="radio" name="con-equality" value="!!" /><tt>!!</tt></li>
    <li><input type="radio" name="con-equality" value="none" />None of the above.</li>
   </ul>
EOT
        evaluate => sub {
            my ($ans) = @_;
            if ($ans eq '==') {
                return "Correct";
            }
            elsif ($ans eq '=') {
                return "Incorrect.  I know the question is a little ambiguous, " .
                       "because of course = represents equality.  But this is a question " .
                       "from your exam!  What she means here is an 'equality <i>test</i>' " .
                       "as opposed to 'assignment' (changing the value of a variable). " .
                       "The single = changes its left side, the double == just evaluates " .
                       "to true or false based on whether its two sides are the same.";
            }
            else {
                return "Incorrect. The correct answer is ==.";
            }
        },
    },

#####################
    'app-equality' => {
        text => <<'EOT',
   <pre>
    int main()
    {
        int x = 0;
        x == 42;
        cout &lt;&lt; x;
        return 0;
    }
   </pre>
   What is the output of running this program (write "error" followed by a 
   reason if there is a compile error)? <br/>
   <input type="text" name="app-equality" size="60"/>
EOT
        evaluate => sub {
            my ($ans) = @_;
            if ($ans eq '0') {
                return "Correct";
            }
            if ($ans eq '42') {
                return "Incorrect.  This was kind of a trick question in that " .
                       "the only thing it could mean to a reasonable human is " .
                       "not what it means to the computer.  The trick is that " .
                       "== is the equality <i>test</i> operator, so you are just " .
                       "asking whether x is 42, and not changing anything.  If " .
                       "you wanted to change x, you should have used the single " .
                       "equals sign (assignment operator).  Keep your eye open " .
                       "for such trickery on the test.  The correct answer is 0.";
            }
            return "Incorrect. The correct answer is 0.";
        },
    },
);

my $cgi = CGI->new;

my %answers;
for my $param ($cgi->param) {
    my $value = $cgi->param($param);
    
    next unless $value =~ /\S/;
    $value =~ s/^\s*//;
    $value =~ s/\s*$//;
    
    if ($param =~ /^(.*):(.*)$/) {
        $answers{$1}{$2} = $value;
    }
    else {
        $answers{$param} = $value;
    }
}

$answers{SEED} ||= 1 + int rand 100000;
srand($answers{SEED});

print <<"EOT";
Content-type: text/html

<html>
<head>
 <title> CSCI 1300 Concept-Application Test </title>
 <style>
  table.ident {
   margin-left: 1in;
   background: #ddd;
   border: 1px black solid;
   border-collapse: separate;
   border-spacing: 4mm;
  }

  div.problem {
   margin-left: 1in;
   width: 6.5in;
   margin-top: 2ex;
   padding: 2mm;
   background: #ccf;
   border: 1px black solid;
  }
  div.explanation {
   width: 6.5in;
   margin-top: 4ex;
   margin-left: 1in;
  }

  div.correct {
   margin-left: 0.5in;
   width: 4in;
   margin-top: 2ex;
   padding: 2mm;
   background: #cfc;
   border: 1px black solid;
  }
  div.incorrect {
   margin-left: 0.5in;
   width: 4in;
   margin-top: 2ex;
   padding: 2mm;
   background: #faa;
   border: 1px black solid;
  }
 </style>
</head>
<body>
 <form action="index.pl" method="post">
  <input type="hidden" name="SEED" value="$answers{SEED}" />

  <div class="explanation">
   <p><b>Try to answer all the questions in the test before pushing "Submit"
    at the bottom.  When you do submit, you will see a page indicating which
    problems you got wrong and an explanation about what is going on in 
    the problem.</b></p>
   <p><b>Assume that the following two lines are at the top of every program:</b></p>
   <pre>
    #include &lt;iostream&gt;
    using namespace std;
   </pre>
  </div>

  <table class="ident">
   <tr>
    <td>Full name:</td>
    <td><input type="text" name="fullname" /></td>
   </tr>
   <tr>
    <td>Student ID:</td>
    <td><input type="text" name="studentid" /></td>
   </tr>
  </table>
  
EOT

for my $problem (shuffle(keys %problems)) {
    print <<"EOT";
  <div class="problem">
$problems{$problem}{text}
EOT

    if (exists $answers{$problem}) {
        my $ans = $problems{$problem}{evaluate}->($answers{$problem});
        if ($ans eq 'Correct' || $ans =~ /^Almost correct/) {
            print "<div class=\"correct\">\n$ans\n</div>\n";
        }
        else {
            print "<div class=\"incorrect\">\n";
            if (!ref $answers{$problem}) {
                print "Your answer was <b>$answers{$problem}</b>.<br/>\n";
            }
            print "$ans\n</div>\n";
        }

    }
    print "  </div>\n";
}

print <<'EOT';
 <div class="explanation">
  <center><input type="submit" value="Submit" style="font-size: 20pt"/></center>
 </div>
 </form>
</body>
</html>
EOT

if ($cgi->param) {
    my $surveyno = "0000";
    $surveyno++ while -e "data/survey_$surveyno";
    open my $fh, '>', "data/survey_$surveyno" or die "Damn, opening data/survey_$surveyno failed: $!";
    print $fh Dumper(\%answers);
    close $fh;
}
