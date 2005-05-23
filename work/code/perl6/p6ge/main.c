#include "p6ge.h"
#include <malloc.h>
#include <stdio.h>

int 
main(int argc,char* argv[]) 
{
    char pattern[256];
    P6RuleText* rtext = 0;
    P6Rule* rexp = 0;
    p6ge_init();
    rtext = malloc(sizeof(*rtext));
    while (fgets(pattern, sizeof(pattern), stdin)) {
        rtext->text = pattern;
        rtext->pos = rtext->text;
        rexp = p6ge_parse(rtext);
        if (rexp) {
            p6ge_printexp(stdout, rexp, 0);
        }
        else {
            printf("Parse aborted.\n");
        }
    }
    return 0;
}
