# A viewed input survives a modeled pthread create and join

The parent holds a view of one cell. A successful creation lends one reader
share and the join returns it. This pins the contract-certification boundary
for source-level pthread transitions on a viewed input.

```c filename=modeled_pthread_shared_reader_single.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *reader(void *p) {
    struct cell *q = p;
    int observed = q->value;
    return NULL;
}

int run(struct cell *task) {
    pthread_t first;
    if (pthread_create(&first, NULL, reader, task) != 0) {
        return 0;
    }
    (void)pthread_join(first, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_reader_single.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *task) {
    views task->value;
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
