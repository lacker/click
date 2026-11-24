# A worker cannot consume population authority

A worker may borrow authority with `owns` and return it at join. Retiring the
authority in a worker would end the population while the parent still expects
it back, so the worker contract is refused at create.

```c filename=modeled_pthread_worker_consumes_authority_rejected.c
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
verifying "modeled_pthread_worker_consumes_authority_rejected.c";
authorized resource ticket(p: void*) {}
void* worker(void* argument) {
    consumes authority(ticket(argument));
    requires count(ticket(argument)) == 0;
} by { unfold(authority(ticket(argument))); }
int32 run(void* p) {
    consumes authority(ticket(p));
    requires count(ticket(p)) == 0;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch { true => { unfold(authority(ticket(p))); step(); close(); } false => {} }
    step();
    step();
    close();
}
```

```expect
fail: `worker.contract` setup failed: could not evaluate the contract entry resources: function contract could not be applied: Requires owns authority(ticket(...))
```
