# A pthread handle survives copying, forwarding and overwriting its original slot

The ordinary C `pthread_t` value carries creation identity. Copying it does not
copy the completion right consumed by join.

```c filename=modeled_pthread_copied_handle.c
#include <pthread.h>
#include <stddef.h>

struct cell { int value; };
void *worker(void *p) {
    struct cell *q = p;
    q->value = 77;
    return NULL;
}
pthread_t forward(pthread_t h) { return h; }
int run(struct cell *p) {
    pthread_t h;
    if (pthread_create(&h, NULL, worker, p) != 0) return 0;
    pthread_t saved = forward(h);
    h = 0;
    pthread_join(saved, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_copied_handle.c";

void *worker(void *p) { owns (p as (struct cell *))->value; }

uint64 forward(uint64 h) {
    ensures result == h;
}

int32 run(struct cell *p) {
    owns p->value;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    mark created;
    step();
    step();
    step();
    have saved == at(created, h) by close();
    step();
    have saved == at(created, h) by close();
    step();
    step();
    close();
}
```

```expect
pass
```
