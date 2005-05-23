use 5.006001;
use ExtUtils::MakeMaker;

WriteMakefile(
    NAME              => 'Class::Abstract',
    VERSION_FROM      => 'lib/Class/Abstract.pm',
    PREREQ_PM         => { Bit::Vector => 0, Regexp::Common => 0 },
    ABSTRACT_FROM  => 'lib/Class/Abstract.pm',
    AUTHOR         => 'Luke Palmer <fibonaci@localdomain>',
);
