# A disjoint store survives a pending pthread create

The parent owns two separate cells. The worker may mutate one; the parent
updates the other before testing the create status. Both outcomes retain the
parent's unrelated store, and only success creates a completion right.

```c filename=modeled_pthread_disjoint_pending_store.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *worker(void *p) {
    struct cell *q = p;
    q->value = 77;
    return NULL;
}

int run(struct cell *job, struct cell *unrelated) {
    pthread_t h;
    int rc = pthread_create(&h, NULL, worker, job);
    unrelated->value = 7;
    if (rc != 0) return 0;
    pthread_join(h, NULL);
    return unrelated->value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_disjoint_pending_store.c";

void *worker(void *p) {
    owns ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *job, struct cell *unrelated) {
    owns job->value;
    owns unrelated->value;
    ensures result == 0 or result == 7;
    ensures unrelated->value == 7;
} by {
    step();
    step();
    step();
    step();
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
