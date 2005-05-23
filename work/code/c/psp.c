#include <stdio.h>

void fucker(int offs)
{
    char foo = 'x';
    char* bar = &foo;
    bar += offs;
    *bar = 'g';
}

int main()
{
    char ch = 'f';

    printf("%c\n", ch);
    fucker(32);
    printf("%c\n", ch);
}
