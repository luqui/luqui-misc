#include "p6ge.h"
#include <stdio.h>
#include <ctype.h>
#include <malloc.h>
#include <string.h>

void p6ge_init() 
{
    unsigned int c;
    for(c=0;c<256;c++) {
        if (isspace(c)) p6ge_ctype[c] |= ctmeta | ctspace;
        p6ge_slashmeta[c] = (!isalnum(c)) ? c : -1;
    }
    p6ge_ctype[0] |= ctmeta | ctket;
    p6ge_ctype['('] |= ctmeta;
    p6ge_ctype[')'] |= ctmeta | ctket;
    p6ge_ctype['['] |= ctmeta;
    p6ge_ctype[']'] |= ctmeta | ctket;
    p6ge_ctype['<'] |= ctmeta;
    p6ge_ctype['>'] |= ctmeta | ctket;
    p6ge_ctype['#'] |= ctmeta;
    p6ge_ctype['^'] |= ctmeta;
    p6ge_ctype['$'] |= ctmeta;
    p6ge_ctype[':'] |= ctmeta;
    p6ge_ctype['\\'] |= ctmeta;
    p6ge_ctype['|'] |= ctmeta | ctket;
    p6ge_ctype['&'] |= ctmeta | ctket;
    p6ge_ctype['.'] |= ctmeta;
    p6ge_ctype['*'] |= ctmeta | ctquant;
    p6ge_ctype['+'] |= ctmeta | ctquant;
    p6ge_ctype['?'] |= ctmeta | ctquant;
    p6ge_slashmeta['d'] = -1;
    p6ge_slashmeta['D'] = -1;
    p6ge_slashmeta['n'] = '\n';
    p6ge_slashmeta['N'] = -1;
    p6ge_slashmeta['b'] = -1;
    p6ge_slashmeta['B'] = -1;
    p6ge_slashmeta['r'] = '\r';
    p6ge_slashmeta['t'] = '\t';
    p6ge_slashmeta['f'] = '\f';
    p6ge_slashmeta['v'] = '\v';
    p6ge_slashmeta['0'] = '\0';
}


P6Rule* 
p6ge_newexp(p6ge_exp_t type, P6Rule* exp1, P6Rule* exp2)
{
    P6Rule* rc = 0;
    rc = malloc(sizeof(*rc));
    rc->type = type;
    rc->min = 1;
    rc->max = 1;
    rc->ismaximal = 1;
    rc->exp1 = exp1;
    rc->exp2 = exp2;
    rc->name = 0;
    rc->nlen = 0;
    return rc;
}
    

void 
p6ge_skip(P6RuleText* rtext, int skip) 
{
    const unsigned char* s = rtext->pos + skip;
    while (p6ge_ctype[*s] & ctspace) s++;
    while (*s=='#') {
      s++;
      while (*s && *s!='\n') s++;
      while (p6ge_ctype[*s] & ctspace) s++;
    }
    rtext->pos = s;
}


void
p6ge_parse_error(P6RuleText* rtext, const char* msg)
{
    printf("%s at offset %d (found '%c')\n", msg,
            rtext->pos - rtext->text, *(rtext->pos));
    rtext->pos="";
}


P6Rule*
p6ge_parse_literal(P6RuleText* rtext)
{
    static unsigned char lit[1024];
    P6Rule* rexp = 0;
    int len = 0;
    int c;

    while (len<sizeof(lit) && (c=*(rtext->pos))) { 
        if ((p6ge_ctype[c] & ctmeta)==0) 
            { lit[len++]=c; p6ge_skip(rtext, 1); }
        else if (c=='\\' && p6ge_slashmeta[rtext->pos[1]]>=0)
            { lit[len++]=p6ge_slashmeta[rtext->pos[1]]; p6ge_skip(rtext, 2); }
        else break;
    }
    if (len>0) {
        rexp = p6ge_newexp(P6GE_LITERAL, 0, 0);
        rexp->name = malloc(len); rexp->nlen=len;
        memcpy(rexp->name, lit, len);
    }
    return rexp;
}


P6Rule*
p6ge_parse_assert(P6RuleText* rtext)
{
    P6Rule* rexp = 0;
    int negate = ' ';
    int npos;
    p6ge_skip(rtext, 1);
    if (*(rtext->pos)=='!') { negate='!'; p6ge_skip(rtext, 1); }
    npos = 0;
    while (isalnum(rtext->pos[npos])) npos++;
    if (npos>0) {
        if (strncmp("before", rtext->pos, 6)==0 ||
                strncmp("after", rtext->pos, 5)==0) {
            const char* name = rtext->pos;
            p6ge_skip(rtext, npos);
            rexp = p6ge_newexp(P6GE_LOOKAROUND, p6ge_parse(rtext), 0);
            rexp->sigil = *name;
            rexp->name = malloc(npos); rexp->nlen=npos;
            memcpy(rexp->name, name, npos);
        } else {
            rexp = p6ge_newexp(P6GE_ASSERT, 0, 0);
            rexp->name = malloc(npos); rexp->nlen=npos;
            memcpy(rexp->name, rtext->pos, npos);
            p6ge_skip(rtext, npos);
        }
    }
    if (rexp) rexp->negate=negate;
    if (*(rtext->pos)!='>') p6ge_parse_error(rtext, "Missing >");
    else p6ge_skip(rtext, 1);
    return rexp;
}  
       
 
P6Rule*
p6ge_parse_term(P6RuleText* rtext)
{
    int c;
    int ctype;
    P6Rule* rexp = 0;

    p6ge_skip(rtext, 0);
    c = *(rtext->pos);
    ctype = p6ge_ctype[c];
    if ((ctype & ctmeta)==0 ||
            (c=='\\' && p6ge_slashmeta[rtext->pos[1]]>=0))
        return p6ge_parse_literal(rtext);
    if (c==0) return 0;
    if (c=='\\') {
        rexp = p6ge_newexp(P6GE_ESCAPE, 0, 0);
        rexp->sigil = rtext->pos[1];
        p6ge_skip(rtext, 2);
        return rexp;
    }
    if (c=='(' || c=='[') {
        char ket = (c=='(') ? ')' : ']';
        p6ge_skip(rtext, 1);
        rexp = p6ge_newexp(P6GE_GROUP, p6ge_parse(rtext), 0);
        rexp->sigil = c;
        if (*(rtext->pos)!=ket) p6ge_parse_error(rtext, "Missing ')' or ']'");
        else p6ge_skip(rtext, 1);
        return rexp;
    }
    if (c=='<') return p6ge_parse_assert(rtext);
    if (c==':') {
        if (rtext->pos[1]==':') {
            p6ge_skip(rtext, 2);
            return p6ge_newexp(P6GE_DOUBLECUT, 0, 0);
        }
        p6ge_skip(rtext, 1);
        return p6ge_newexp(P6GE_CUT, 0, 0);
    }
    p6ge_parse_error(rtext, "Unrecognized character");
    return 0;
}


P6Rule*
p6ge_parse_quant(P6RuleText* rtext)
{
    P6Rule* rexp = p6ge_parse_term(rtext);
    P6Rule* qexp = rexp;
    int c = *(rtext->pos);
    if ((p6ge_ctype[c] & ctquant)==0) return rexp;
    p6ge_skip(rtext, 1);

    /* if quantifying a literal string, quantifier only applies to last
       char */
    if (rexp->type==P6GE_LITERAL && rexp->nlen>1) {
        rexp->nlen--;
        qexp = p6ge_newexp(P6GE_LITERAL, 0, 0);
        qexp->name = malloc(1); qexp->nlen=1; 
        qexp->name[0] = rexp->name[rexp->nlen];
        rexp = p6ge_newexp(P6GE_CONCAT, rexp, qexp);
    }

    if (c=='+') qexp->max=-1; 
    else if (c=='?') qexp->min=0; 
    else if (*(rtext->pos)!='*') { qexp->min=0; qexp->max=-1; }
    else {
        p6ge_skip(rtext, 1);
        if (*(rtext->pos)!='{') 
            p6ge_parse_error(rtext, "Missing { after ** quantifier");
        p6ge_skip(rtext, 1);
        if (isdigit(*(rtext->pos))) {
            qexp->min = qexp->max = atoi(rtext->pos);
            while(isdigit(*(rtext->pos))) rtext->pos++;
            p6ge_skip(rtext, 0);
        } else p6ge_parse_error(rtext, "Missing min value after **{");
        if (rtext->pos[0]=='.' && rtext->pos[1]=='.') {
            p6ge_skip(rtext, 2);
            if (rtext->pos[0]=='.') { qexp->max=-1; p6ge_skip(rtext, 1); }
            else if (isdigit(*(rtext->pos))) {
                qexp->max = atoi(rtext->pos);
                while(isdigit(*(rtext->pos))) rtext->pos++;
                p6ge_skip(rtext, 0);
          } else p6ge_parse_error(rtext, "Missing max value after '..'");
        }
        if (*(rtext->pos)!='}')
            p6ge_parse_error(rtext, "Missing closing '}'");
        else p6ge_skip(rtext, 1);
    }
    if (*(rtext->pos)=='?') { qexp->ismaximal=0; p6ge_skip(rtext, 1); }
    return rexp;
}


P6Rule*
p6ge_parse_concat(P6RuleText* rtext)
{
    P6Rule* rexp = p6ge_parse_quant(rtext);
    if ((p6ge_ctype[*(rtext->pos)] & ctket)==0)
        rexp = p6ge_newexp(P6GE_CONCAT, rexp, p6ge_parse_concat(rtext));
    return rexp;
}


P6Rule*
p6ge_parse_mult(P6RuleText* rtext)
{
    P6Rule* rexp = p6ge_parse_concat(rtext);
    if (*(rtext->pos)=='&') {
        p6ge_skip(rtext, 1);
        rexp = p6ge_newexp(P6GE_MULT, rexp, p6ge_parse_mult(rtext));
    }
    return rexp;
}

P6Rule*
p6ge_parse_alt(P6RuleText* rtext)
{
    P6Rule* rexp = p6ge_parse_mult(rtext);
    if (*(rtext->pos)=='|') {
        p6ge_skip(rtext, 1);
        rexp = p6ge_newexp(P6GE_ALT, rexp, p6ge_parse_alt(rtext));
    }
    return rexp;
}

P6Rule*
p6ge_parse(P6RuleText* rtext)
{
    P6Rule* rexp = 0;
    rexp = p6ge_parse_alt(rtext);
    return rexp;
}


void 
p6ge_printexp(FILE* fp, P6Rule* rexp, int depth)
{
    int indent;
    char* msg;
    indent = depth*4;
    char quant[64];
    if (rexp->max<0) sprintf(quant, "{%d..Inf}", rexp->min);
    else sprintf(quant, "{%d..%d}", rexp->min, rexp->max);
    if (!rexp->ismaximal) strcat(quant, "?");
    switch (rexp->type) {
    case P6GE_CONCAT:
        p6ge_printexp(fp, rexp->exp1, depth);
        p6ge_printexp(fp, rexp->exp2, depth);
        break;
    case P6GE_ASSERT:
        fprintf(fp, "%*sassert %c<%.*s> %s\n", indent, "",
                rexp->negate, rexp->nlen, rexp->name, quant);
        break;
    case P6GE_LOOKAROUND:
        fprintf(fp, "%*sLOOK%.*s %c %s\n", indent, "", rexp->nlen, rexp->name,
                rexp->negate, quant);
        p6ge_printexp(fp, rexp->exp1, depth+1);
        break;
    case P6GE_GROUP:
        fprintf(fp, "%*sGROUP%c\n", indent, "", rexp->sigil, quant);
        p6ge_printexp(fp, rexp->exp1, depth+1);
        fprintf(fp, "%*s%c %s\n", indent, "", (rexp->sigil=='(') ? ')' : ']', quant);
        break;
    case P6GE_ALT:
        p6ge_printexp(fp, rexp->exp1, depth+1);
        fprintf(fp, "%*sOR\n", indent, "");
        p6ge_printexp(fp, rexp->exp2, depth + (rexp->exp2->type != P6GE_ALT));
        break;
    case P6GE_MULT:
        p6ge_printexp(fp, rexp->exp1, depth+1);
        fprintf(fp, "%*sAND\n", indent, "");
        p6ge_printexp(fp, rexp->exp2, depth + (rexp->exp2->type != P6GE_ALT));
        break;
    case P6GE_LITERAL:
        fprintf(fp, "%*sliteral \"%.*s\" %s\n", indent, "",
                rexp->nlen, rexp->name, quant);
        break;
    case P6GE_ESCAPE:
        fprintf(fp, "%*sescape  \\%c %s\n", indent, "", rexp->sigil, quant);
        break;
    case P6GE_CUT:
        fprintf(fp, "%*sCUT\n", indent, "");
        break;
    case P6GE_DOUBLECUT:
        fprintf(fp, "%*sDBLCUT\n", indent, "");
        break;
    }
}

