use 5.006;
use ExtUtils::MakeMaker;
WriteMakefile(
    NAME              => 'glop',
    PREREQ_PM         => { 'SDL' => '1.20' },
    ABSTRACT          => "The Game Language Of Perl distribution",
    AUTHOR            => 'Luke Palmer <fibonaci@nonet>',
);
