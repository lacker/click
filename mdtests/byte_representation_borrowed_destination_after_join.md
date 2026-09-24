# The same copy verifies once the stable view has ended

Control for
[`byte_representation_borrowed_destination_rejected.md`](byte_representation_borrowed_destination_rejected.md):
the identical program with the `memcpy` moved after `pthread_join`. Joining
the worker ends its loan and recovers the caller's escrowed ownership of the
heap cell, so the copy's `owns destination[0..bytes]` precondition holds and
the program verifies.

```c filename=borrowed_destination_after_join.c
#include <pthread.h>
#include <stddef.h>
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);

struct cell { unsigned int value; };

void *reader(void *p) {
    struct cell *q = p;
    unsigned int observed = q->value;
    return NULL;
}

int run(void) {
    struct cell *shared = malloc(sizeof(struct cell));
    if (shared == 0) { return 0; }
    struct cell *update = malloc(sizeof(struct cell));
    if (update == 0) { free(shared); return 0; }
    shared->value = 7u;
    update->value = 9u;
    pthread_t worker;
    if (pthread_create(&worker, NULL, reader, shared) != 0) {
        free(update); free(shared);
        return 0;
    }
    (void)pthread_join(worker, NULL);
    memcpy((unsigned char *)(void *)shared, (unsigned char *)(void *)update, sizeof(struct cell));
    free(update); free(shared);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "borrowed_destination_after_join.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run() {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
