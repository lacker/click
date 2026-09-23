# A delayed pthread create status selects its checked outcome

The modeled runtime is an explicit assumption. The worker is verified from its
ordinary C body. The parent may copy the create status and update an unrelated
scalar before branching; only the successful path receives a completion right.

```c filename=modeled_pthread_delayed_create.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };

void *worker(void *p) {
    struct cell *q = p;
    q->value = 77;
    return NULL;
}

int run(struct cell *p) {
    pthread_t h;
    int rc = pthread_create(&h, NULL, worker, p);
    int saved = rc;
    int unrelated = 7;
    if (saved != 0) return 0;
    pthread_join(h, NULL);
    return unrelated;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "modeled_pthread_delayed_create.c";

void *worker(void *p) {
    owns ((struct cell *)p)->value;
} by {
    execute();
    simp();
}

int32 run(struct cell *p) {
    owns p->value;
    ensures result == 0 or result == 7;
} by {
    step();
    step();
    step();
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
