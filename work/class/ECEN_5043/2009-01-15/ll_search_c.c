#include <stdio.h>
#include <stdlib.h>

struct LinkedList {
    int contents;
    struct LinkedList* next;
};

struct LinkedList* fill_list(int size, int max) {
    struct LinkedList* head;
    struct LinkedList* cur;

    head = cur = (struct LinkedList*)malloc(sizeof(struct LinkedList));
    head->contents = rand() % max;
    size--;

    while (size --> 0) {
        struct LinkedList* n = (struct LinkedList*)malloc(sizeof(struct LinkedList));
        n->contents = rand() % max;
        cur->next = n;
        cur = n;
    }
    cur->next = NULL;
    return head;
}

struct LinkedList* fill_list_contiguous(int size, int max) {
    void* mem = malloc(size*sizeof(struct LinkedList));
    struct LinkedList* head;
    struct LinkedList* cur;

    head = cur = (struct LinkedList*)mem;
    head->contents = rand() % max;
    mem += sizeof(struct LinkedList);
    size--;

    while (size --> 0) {
        struct LinkedList* n = (struct LinkedList*)mem;
        n->contents = rand() % max;
        cur->next = n;
        cur = n;
        mem += sizeof(struct LinkedList);
    }
    cur->next = NULL;
    return head;
}

int search_list(int elem, struct LinkedList* list) {
    while (list) {
        if (elem == list->contents) {
            return 1;
        }
        list = list->next;
    }
    return 0;
}

void usage() {
    printf("Usage: ll_search_c <malloc|contiguous> size max iters\n");
    exit(1);
}

int main(int argc, char** argv) {
    if (argc != 5) {
        usage();
    }
    int size  = atoi(argv[2]);
    int max   = atoi(argv[3]);
    int iters = atoi(argv[4]);

    struct LinkedList* ll;
    if (strcmp(argv[1], "malloc") == 0) {
        ll = fill_list(size, max);
    }
    else if (strcmp(argv[1], "contiguous") == 0) {
        ll = fill_list_contiguous(size, max);
    }
    else {
        usage();
    }

    int trues = 0;
    while (iters --> 0) {
        int sfor = rand() % max;
        int result = search_list(sfor, ll);
        if (result) { trues++; }
    }

    printf("%d elements found\n", trues);
}
