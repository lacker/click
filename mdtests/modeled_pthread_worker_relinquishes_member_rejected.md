# A worker without authority cannot keep a lent member

The worker declares that it consumes the parent's member but holds no
authority, so it cannot spend it. Ending with the member unreturned would
hide it from the population, so the worker contract is refused.

```c filename=modeled_pthread_worker_relinquishes_member_rejected.c
#include <pthread.h>
#include <stddef.h>
void *worker(void *argument) { return NULL; }
int run(void *p) {
    pthread_t handle;
    if (pthread_create(&handle, NULL, worker, p) != 0) return 0;
    (void)pthread_join(handle, NULL);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_worker_relinquishes_member_rejected.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    consumes ticket(argument);
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
    close();
}
```

```expect
fail: helper contract needs conserved owns resources, a checked consumes/produces effect, or a supported unit exchange
```
