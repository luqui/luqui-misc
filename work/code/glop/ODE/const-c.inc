#ifndef dContactMu2
# define dContactMu2 dContactMu2
#endif
#ifndef dContactFDir1
# define dContactFDir1 dContactFDir1
#endif
#ifndef dContactBounce
# define dContactBounce dContactBounce
#endif
#ifndef dContactSoftERP
# define dContactSoftERP dContactSoftERP
#endif
#ifndef dContactSoftCFM
# define dContactSoftCFM dContactSoftCFM
#endif
#ifndef dContactMotion1
# define dContactMotion1 dContactMotion1
#endif
#ifndef dContactMotion2
# define dContactMotion2 dContactMotion2
#endif
#ifndef dContactSlip1
# define dContactSlip1 dContactSlip1
#endif
#ifndef dContactSlip2
# define dContactSlip2 dContactSlip2
#endif
#ifndef dContactApprox1_1
# define dContactApprox1_1 dContactApprox1_1
#endif
#ifndef dContactApprox1_2
# define dContactApprox1_2 dContactApprox1_2
#endif
#ifndef dContactApprox1
# define dContactApprox1 dContactApprox1
#endif
#ifndef dParamLoStop
# define dParamLoStop dParamLoStop
#endif
#ifndef dParamHiStop
# define dParamHiStop dParamHiStop
#endif
#ifndef dParamVel
# define dParamVel dParamVel
#endif
#ifndef dParamFMax
# define dParamFMax dParamFMax
#endif
#ifndef dParamFudgeFactor
# define dParamFudgeFactor dParamFudgeFactor
#endif
#ifndef dParamBounce
# define dParamBounce dParamBounce
#endif
#ifndef dParamCFM
# define dParamCFM dParamCFM
#endif
#ifndef dParamStopERP
# define dParamStopERP dParamStopERP
#endif
#ifndef dParamStopCFM
# define dParamStopCFM dParamStopCFM
#endif
#ifndef dParamSuspensionERP
# define dParamSuspensionERP dParamSuspensionERP
#endif
#ifndef dParamSuspensionCFM
# define dParamSuspensionCFM dParamSuspensionCFM
#endif
#define PERL_constant_NOTFOUND	1
#define PERL_constant_NOTDEF	2
#define PERL_constant_ISIV	3
#define PERL_constant_ISNO	4
#define PERL_constant_ISNV	5
#define PERL_constant_ISPV	6
#define PERL_constant_ISPVN	7
#define PERL_constant_ISSV	8
#define PERL_constant_ISUNDEF	9
#define PERL_constant_ISUV	10
#define PERL_constant_ISYES	11

#ifndef NVTYPE
typedef double NV; /* 5.6 and later define NVTYPE, and typedef NV to it.  */
#endif
#ifndef aTHX_
#define aTHX_ /* 5.6 or later define this for threading support.  */
#endif
#ifndef pTHX_
#define pTHX_ /* 5.6 or later define this for threading support.  */
#endif

static int
constant_12 (pTHX_ const char *name, IV *iv_return) {
  /* When generated this function returned values for the list of names given
     here.  However, subsequent manual editing may have added or removed some.
     dParamBounce dParamHiStop dParamLoStop */
  /* Offset 6 gives the best switch position.  */
  switch (name[6]) {
  case 'B':
    if (memEQ(name, "dParamBounce", 12)) {
    /*                     ^            */
#ifdef dParamBounce
      *iv_return = dParamBounce;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'H':
    if (memEQ(name, "dParamHiStop", 12)) {
    /*                     ^            */
#ifdef dParamHiStop
      *iv_return = dParamHiStop;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'L':
    if (memEQ(name, "dParamLoStop", 12)) {
    /*                     ^            */
#ifdef dParamLoStop
      *iv_return = dParamLoStop;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  }
  return PERL_constant_NOTFOUND;
}

static int
constant_13 (pTHX_ const char *name, IV *iv_return) {
  /* When generated this function returned values for the list of names given
     here.  However, subsequent manual editing may have added or removed some.
     dContactFDir1 dContactSlip1 dContactSlip2 dParamStopCFM dParamStopERP */
  /* Offset 12 gives the best switch position.  */
  switch (name[12]) {
  case '1':
    if (memEQ(name, "dContactFDir", 12)) {
    /*                           1      */
#ifdef dContactFDir1
      *iv_return = dContactFDir1;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    if (memEQ(name, "dContactSlip", 12)) {
    /*                           1      */
#ifdef dContactSlip1
      *iv_return = dContactSlip1;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case '2':
    if (memEQ(name, "dContactSlip", 12)) {
    /*                           2      */
#ifdef dContactSlip2
      *iv_return = dContactSlip2;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'M':
    if (memEQ(name, "dParamStopCF", 12)) {
    /*                           M      */
#ifdef dParamStopCFM
      *iv_return = dParamStopCFM;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'P':
    if (memEQ(name, "dParamStopER", 12)) {
    /*                           P      */
#ifdef dParamStopERP
      *iv_return = dParamStopERP;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  }
  return PERL_constant_NOTFOUND;
}

static int
constant_15 (pTHX_ const char *name, IV *iv_return) {
  /* When generated this function returned values for the list of names given
     here.  However, subsequent manual editing may have added or removed some.
     dContactApprox1 dContactMotion1 dContactMotion2 dContactSoftCFM
     dContactSoftERP */
  /* Offset 14 gives the best switch position.  */
  switch (name[14]) {
  case '1':
    if (memEQ(name, "dContactApprox", 14)) {
    /*                             1      */
#ifdef dContactApprox1
      *iv_return = dContactApprox1;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    if (memEQ(name, "dContactMotion", 14)) {
    /*                             1      */
#ifdef dContactMotion1
      *iv_return = dContactMotion1;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case '2':
    if (memEQ(name, "dContactMotion", 14)) {
    /*                             2      */
#ifdef dContactMotion2
      *iv_return = dContactMotion2;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'M':
    if (memEQ(name, "dContactSoftCF", 14)) {
    /*                             M      */
#ifdef dContactSoftCFM
      *iv_return = dContactSoftCFM;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'P':
    if (memEQ(name, "dContactSoftER", 14)) {
    /*                             P      */
#ifdef dContactSoftERP
      *iv_return = dContactSoftERP;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  }
  return PERL_constant_NOTFOUND;
}

static int
constant_17 (pTHX_ const char *name, IV *iv_return) {
  /* When generated this function returned values for the list of names given
     here.  However, subsequent manual editing may have added or removed some.
     dContactApprox1_1 dContactApprox1_2 dParamFudgeFactor */
  /* Offset 16 gives the best switch position.  */
  switch (name[16]) {
  case '1':
    if (memEQ(name, "dContactApprox1_", 16)) {
    /*                               1      */
#ifdef dContactApprox1_1
      *iv_return = dContactApprox1_1;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case '2':
    if (memEQ(name, "dContactApprox1_", 16)) {
    /*                               2      */
#ifdef dContactApprox1_2
      *iv_return = dContactApprox1_2;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 'r':
    if (memEQ(name, "dParamFudgeFacto", 16)) {
    /*                               r      */
#ifdef dParamFudgeFactor
      *iv_return = dParamFudgeFactor;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  }
  return PERL_constant_NOTFOUND;
}

static int
constant (pTHX_ const char *name, STRLEN len, IV *iv_return) {
  /* Initially switch on the length of the name.  */
  /* When generated this function returned values for the list of names given
     in this section of perl code.  Rather than manually editing these functions
     to add or remove constants, which would result in this comment and section
     of code becoming inaccurate, we recommend that you edit this section of
     code, and use it to regenerate a new set of constant functions which you
     then use to replace the originals.

     Regenerate these constant functions by feeding this entire source file to
     perl -x

#!perl -w
use ExtUtils::Constant qw (constant_types C_constant XS_constant);

my $types = {map {($_, 1)} qw(IV)};
my @names = (qw(dContactApprox1 dContactApprox1_1 dContactApprox1_2
	       dContactBounce dContactFDir1 dContactMotion1 dContactMotion2
	       dContactMu2 dContactSlip1 dContactSlip2 dContactSoftCFM
	       dContactSoftERP dParamBounce dParamCFM dParamFMax
	       dParamFudgeFactor dParamHiStop dParamLoStop dParamStopCFM
	       dParamStopERP dParamSuspensionCFM dParamSuspensionERP dParamVel));

print constant_types(); # macro defs
foreach (C_constant ("ODE", 'constant', 'IV', $types, undef, 3, @names) ) {
    print $_, "\n"; # C constant subs
}
print "#### XS Section:\n";
print XS_constant ("ODE", $types);
__END__
   */

  switch (len) {
  case 9:
    /* Names all of length 9.  */
    /* dParamCFM dParamVel */
    /* Offset 6 gives the best switch position.  */
    switch (name[6]) {
    case 'C':
      if (memEQ(name, "dParamCFM", 9)) {
      /*                     ^        */
#ifdef dParamCFM
        *iv_return = dParamCFM;
        return PERL_constant_ISIV;
#else
        return PERL_constant_NOTDEF;
#endif
      }
      break;
    case 'V':
      if (memEQ(name, "dParamVel", 9)) {
      /*                     ^        */
#ifdef dParamVel
        *iv_return = dParamVel;
        return PERL_constant_ISIV;
#else
        return PERL_constant_NOTDEF;
#endif
      }
      break;
    }
    break;
  case 10:
    if (memEQ(name, "dParamFMax", 10)) {
#ifdef dParamFMax
      *iv_return = dParamFMax;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 11:
    if (memEQ(name, "dContactMu2", 11)) {
#ifdef dContactMu2
      *iv_return = dContactMu2;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 12:
    return constant_12 (aTHX_ name, iv_return);
    break;
  case 13:
    return constant_13 (aTHX_ name, iv_return);
    break;
  case 14:
    if (memEQ(name, "dContactBounce", 14)) {
#ifdef dContactBounce
      *iv_return = dContactBounce;
      return PERL_constant_ISIV;
#else
      return PERL_constant_NOTDEF;
#endif
    }
    break;
  case 15:
    return constant_15 (aTHX_ name, iv_return);
    break;
  case 17:
    return constant_17 (aTHX_ name, iv_return);
    break;
  case 19:
    /* Names all of length 19.  */
    /* dParamSuspensionCFM dParamSuspensionERP */
    /* Offset 16 gives the best switch position.  */
    switch (name[16]) {
    case 'C':
      if (memEQ(name, "dParamSuspensionCFM", 19)) {
      /*                               ^         */
#ifdef dParamSuspensionCFM
        *iv_return = dParamSuspensionCFM;
        return PERL_constant_ISIV;
#else
        return PERL_constant_NOTDEF;
#endif
      }
      break;
    case 'E':
      if (memEQ(name, "dParamSuspensionERP", 19)) {
      /*                               ^         */
#ifdef dParamSuspensionERP
        *iv_return = dParamSuspensionERP;
        return PERL_constant_ISIV;
#else
        return PERL_constant_NOTDEF;
#endif
      }
      break;
    }
    break;
  }
  return PERL_constant_NOTFOUND;
}

