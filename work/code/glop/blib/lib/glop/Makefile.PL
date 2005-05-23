use 5.006;
use ExtUtils::MakeMaker;
WriteMakefile(
    NAME              => 'Glop',
    VERSION_FROM      => 'Glop.pm',
    PREREQ_PM         => { ODE => 0, 
                           SDL => '1.20', 
                           Want => 0, 
                           Filter::Simple => 0 
                         },
    ABSTRACT_FROM     => 'Glop.pm',
    AUTHOR            => 'Luke Palmer <fibonaci@nonet>',
);
