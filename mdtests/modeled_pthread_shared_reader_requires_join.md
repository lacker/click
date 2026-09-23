# A shared reader cannot be abandoned after the second create fails

The first create succeeds, then the second fails. Returning without joining
the first child must be rejected while its completion right and reader share
are still live.

```c filename=modeled_pthread_shared_reader_requires_join.c
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
        return 0;
    }
    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_shared_reader_requires_join.c";

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
fail: a function cannot return with a live pthread completion right
```
