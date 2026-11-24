# Overlapping workers of one population cannot both hold its authority

```c filename=modeled_pthread_counted_overlap_rejected.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p, void *q) {
    pthread_t first;
    pthread_t second;
    if (pthread_create(&first, NULL, worker, p) != 0) return 0;
    if (pthread_create(&second, NULL, worker, p) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }
    (void)pthread_join(second, NULL);
    (void)pthread_join(first, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_overlap_rejected.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns authority(ticket(argument));
    owns ticket(argument);
    ensures count(ticket(argument)) >= 1;
}
int32 run(void* p, void* q) {
    owns authority(ticket(p));
    owns authority(ticket(q));
    consumes 2 of ticket(p);
    consumes ticket(q);
    requires p != q;
    requires count(ticket(p)) == 2;
    requires count(ticket(q)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    branch { true => { have count(ticket(p)) == 2; step(); close(); } false => {} }
    step();
    branch {
        true => {
            step();
            have count(ticket(p)) == 0;
            have count(ticket(q)) == 1;
            step(); close();
        }
        false => {}
    }
    step();
    have count(ticket(q)) == 0;
    step();
    have count(ticket(p)) == 0;
    have count(ticket(q)) == 0;
    step(); close();
}
```

```expect
fail: Requires owns authority(ticket(...))
```
