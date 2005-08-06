use 5.006001;
use ExtUtils::MakeMaker;

WriteMakefile(
    NAME              => 'Monad',
    VERSION_FROM      => 'lib/Monad.pm',
    PREREQ_PM         => {},
    ABSTRACT_FROM  => 'lib/Monad.pm',
    AUTHOR         => 'Luke Palmer <lrpalmer@gmail.com>',
);
