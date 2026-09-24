# A stateful counted population cannot move to a worker

The resource definition relates mutable memory to the population count. The
worker handoff rejects that definition even when the worker body does nothing.

```c filename=modeled_pthread_thread_confined_resource_rejected.c
#include <pthread.h>
#include <stddef.h>

struct cell { int refs; };

void *worker(void *argument) {
    return NULL;
}

int run(struct cell *cell) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, cell) != 0) return 0;
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource reference(cell: struct cell*) {
    owns cell->refs;
    fact cell->refs == count(reference(cell));
}
verifying "modeled_pthread_thread_confined_resource_rejected.c";

void *worker(void *argument) {
    owns reference((struct cell *)argument);
} by {
    execute();
    simp();
}

int32 run(struct cell *cell) {
    owns reference(cell);
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: resource `reference` is thread confined and cannot cross a worker boundary
```
