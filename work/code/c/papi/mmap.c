#include <sys/mman.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#define MEMSIZE (1<<23)

void dostuff(char* mem, size_t size)
{ 
    int i, j;
    for (i = 0; i < 100; i++) {
        for (j = 0; j < size; j++) {
            mem[j]++;
        }
    }
}

void measurestuff(const char* desc, char* mem, size_t size) {
    printf("Measuring %s\n", desc);
    dostuff(mem, size);
}

int main() {
    char* mem;

    int pagesize = getpagesize();
    printf("pagesize: %d, alloc: %d\n", pagesize, MEMSIZE);

    mem = malloc(MEMSIZE);
    measurestuff("malloc", mem, MEMSIZE);
    free(mem);

    mem = mmap(0, MEMSIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    measurestuff("mmap", mem, MEMSIZE);
    munmap(mem, MEMSIZE);
}
