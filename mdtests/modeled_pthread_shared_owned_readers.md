# Two workers read one cell supplied as an owned input

The parent lends its cell to both read-only workers and writes only after
both have joined. The source is a synthetic concurrency companion.

```c filename=modeled_pthread_shared_owned_readers.c
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
    pthread_t second;
    if (pthread_create(&first, NULL, reader, task) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, reader, task) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    task->value = 9;
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_owned_readers.c";

void *reader(void *p) {
    views ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *task) {
    owns task->value;
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
