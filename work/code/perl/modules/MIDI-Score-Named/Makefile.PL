use 5.006001;
use ExtUtils::MakeMaker;
# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.
WriteMakefile(
    NAME              => 'MIDI::Score::Named',
    VERSION_FROM      => 'lib/MIDI/Score/Named.pm',
    PREREQ_PM         => {},
    ABSTRACT_FROM     => 'lib/MIDI/Score/Named.pm',
    AUTHOR            => 'Luke Palmer <luke@luqui.org>',
);
