# An abstract resource moves to a worker and returns at join

The abstract resource has no population-wide body. Its ownership is exclusive
for this call, and the checked worker partition moves it to the child until
the join returns it.

```c filename=modeled_pthread_abstract_resource_transfer.c
#include <pthread.h>
#include <stddef.h>

void *worker(void *unused) {
    return NULL;
}

int run(void) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, NULL) != 0) return 0;
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
abstract resource permit();
verifying "modeled_pthread_abstract_resource_transfer.c";

void *worker(void *unused) {
    owns permit();
} by {
    execute();
    simp();
}

int32 run() {
    owns permit();
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
