#include <stdio.h>
#include <stdlib.h>

int* fill_array(int size, int max) {
    int* array = malloc(size*sizeof(int));
    int i;
    for (i = 0; i < size; i++) {
        array[i] = rand() % max;
    }
    return array;
}

int search_array(int elem, int* array, int size) {
    int i;
    for (i = 0; i < size; i++) {
        if (array[i] == elem) {
            return 1;
        }
    }
    return 0;
}

void usage() {
    printf("Usage: array_search_c size max iters\n");
    exit(1);
}

int main(int argc, char** argv) {
    if (argc != 4) {
        usage();
    }
    int size  = atoi(argv[1]);
    int max   = atoi(argv[2]);
    int iters = atoi(argv[3]);

    int* array = fill_array(size, max);
    
    int trues = 0;
    while (iters --> 0) {
        int sfor = rand() % max;
        int result = search_array(sfor, array, size);
        if (result) { trues++; }
    }

    printf("%d elements found\n", trues);
}
