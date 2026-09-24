# A folded exclusive resource moves to a worker and returns at join

The worker holds the whole resource while it runs. Its body stays folded, so
the parent receives the same exclusive authority again at join.

```c filename=modeled_pthread_composite_resource_transfer.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

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
resource cell_at(cell: struct cell*) {
    owns cell->value;
}
verifying "modeled_pthread_composite_resource_transfer.c";

void *worker(void *argument) {
    owns cell_at((struct cell *)argument);
} by {
    execute();
    simp();
}

int32 run(struct cell *cell) {
    owns cell_at(cell);
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
