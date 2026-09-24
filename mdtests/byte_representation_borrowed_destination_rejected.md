# A copy cannot overwrite bytes another thread holds a stable view of

An independent stable borrow, not a read-only contract clause: the caller
owns a heap `struct cell`, and a worker started with `pthread_create` holds
a `views` borrow of its `value` until it is joined. While that loan is live,
the caller's write authority is escrowed in the loan ledger (see
`docs/internals/stable-views.md`), so the `memcpy` that targets the viewed
bytes before the join is refused at its `owns destination[0..bytes]`
precondition. The borrow is not broken, no representation is planted, and
the worker's view stays stable.

Moving the same `memcpy` after `pthread_join` verifies:
[`byte_representation_borrowed_destination_after_join.md`](byte_representation_borrowed_destination_after_join.md)
is that control, so the refusal here comes from the live loan and not from
the copy or its types. The read-only-clause companion is
[`byte_representation_readonly_copy_rejected.md`](byte_representation_readonly_copy_rejected.md).

```c filename=borrowed_destination.c
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
    memcpy((unsigned char *)(void *)shared, (unsigned char *)(void *)update, sizeof(struct cell));
    (void)pthread_join(worker, NULL);
    free(update); free(shared);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "borrowed_destination.c";

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
fail: missing resource fact `owns heap-allocation:1000000@0[0..4]`
```
