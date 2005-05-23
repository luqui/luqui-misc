#ifndef P6GE_H_GUARD
#define P6GE_H_GUARD

#include <stdio.h>

enum { 
    ctliteral=0x00, ctspace=0x01, ctmeta=0x02, ctquant=0x04, 
    ctket=0x08 
};

typedef enum {
    P6GE_LITERAL, P6GE_ESCAPE, P6GE_CONCAT, P6GE_ALT, P6GE_MULT, P6GE_GROUP,
    P6GE_ASSERT, P6GE_LOOKAROUND, P6GE_CUT, P6GE_DOUBLECUT
} p6ge_exp_t;

typedef struct _P6RuleText {
    const unsigned char* text;
    const unsigned char* pos;
} P6RuleText;

typedef struct _P6Rule {
    p6ge_exp_t type;
    int sigil;
    int negate;
    int min;
    int max;
    int ismaximal;
    int nlen;
    struct _P6Rule* exp1;
    struct _P6Rule* exp2;
    unsigned char* name;
} P6Rule;

/* XXX static in .h file!? */
/* These don't seem to be initialized anywhere */
static int p6ge_ctype[256];
static int p6ge_slashmeta[256];

P6Rule* p6ge_parse(P6RuleText* rtext);
void p6ge_init();
void p6ge_printexp(FILE* fp, P6Rule* rexp, int depth);

#endif /* P6GE_H_GUARD */
