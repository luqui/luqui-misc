use 5.006001;
use ExtUtils::MakeMaker;
# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.
WriteMakefile(
    NAME              => 'MIDI::Wire',
    VERSION_FROM      => 'lib/MIDI/Wire.pm',
    PREREQ_PM         => {},
    ABSTRACT_FROM    => 'lib/MIDI/Wire.pm',
    AUTHOR           => 'Luke Palmer <lrpalmer@gmail.com>',
);
