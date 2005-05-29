use 5.006001;
use ExtUtils::MakeMaker;
use ExtUtils::Constant;

our $oderoot =  '../../../../../../ode';

# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.
WriteMakefile(
    NAME              => 'ODE',
    VERSION_FROM      => 'lib/ODE.pm',
    PREREQ_PM         => {},
    ($] >= 5.005 ?
      (ABSTRACT_FROM  => 'lib/ODE.pm',
       AUTHOR         => 'Luke Palmer <fibonaci@flatirons.org>') : ()),
    LIBS              => ['-lstdc++'],
    DEFINE            => '-DHAVE_PLANE2D',
    INC               => "-I. -I$oderoot/include",
    MYEXTLIB          => "$oderoot/lib/libode\$(LIB_EXT)",
    C                 => [ 'ODE.c' ],
    XS                => { 'ODE.xs' => 'ODE.c' },

    clean             => { FILES => "const-c.inc const-c.inc~ const-xs.inc" },
);

my @constants = qw{
    dContactMu2
    dContactFDir1
    dContactBounce
    dContactSoftERP
    dContactSoftCFM
    dContactMotion1
    dContactMotion2
    dContactSlip1
    dContactSlip2
    dContactApprox1_1
    dContactApprox1_2
    dContactApprox1

    dParamLoStop
    dParamHiStop
    dParamVel
    dParamFMax
    dParamFudgeFactor
    dParamBounce
    dParamCFM
    dParamStopERP
    dParamStopCFM
    dParamSuspensionERP
    dParamSuspensionCFM
};

ExtUtils::Constant::WriteConstants(
        NAME  => 'ODE',
        NAMES => \@constants,
        DEFAULT_TYPE => 'IV',
        C_FILE => 'const-c.inc',
        XS_FILE => 'const-xs.inc',
);

{
    # Hack it so that I can use non-#defined constants
    rename 'const-c.inc' => 'const-c.inc~';
    open my $in, '<', 'const-c.inc~' or die "Couldn't open const-c.inc~: $!";
    open my $out, '>', 'const-c.inc' or die "Couldn't write to const-c.inc: $!";

    for (@constants) {
        print $out <<EOC;
#ifndef $_
# define $_ $_
#endif
EOC
    }
    print $out (<$in>);
}

sub MY::postamble {
    return <<'MAKE_EXT';
%.xs: %.odexs odexs2xs.pl
	$(PERL) odexs2xs.pl $< > $@
MAKE_EXT
}
