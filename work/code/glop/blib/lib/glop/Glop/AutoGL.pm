package Glop::AutoGL;

use Glop ();
use Filter::Simple;

FILTER sub {
        s{ (?<![:\w\$@%&])            # not a part of a larger perl word
           (glu?[A-Z]\w* (?= \s* \( ) # a function call
           | GL_[A-Z0-9_]+)           # or a gl constant
         }         
         {Glop::GLSpace::$1}gx;
    };
