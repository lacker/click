# A helper cannot observe an outstanding worker’s Count

```c filename=modeled_pthread_counted_pending_helper.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
void observe(void *p) {}
int run(void *p) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, p) != 0) return 0;
    observe(p);
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_counted_pending_helper.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    owns authority(ticket(argument));
    consumes ticket(argument);
} by { unfold(ticket(argument)); }
void observe(void* p) {
    owns authority(ticket(p));
    ensures 1 == 1;
    requires count(ticket(p)) == 1;
}
int32 run(void* p) {
    owns authority(ticket(p));
    consumes ticket(p);
    requires count(ticket(p)) == 1;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch { true => { unfold(ticket(p)); step(); close(); } false => {} }
    step();
    step();
    step();
    close();
}
```

```expect
fail: Requires owns authority(ticket(...))
```
