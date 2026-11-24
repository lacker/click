# Typed release requires the protected state as an input

The guard alone does not own the protected memory.

```c filename=missing_state.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
void release(struct counter *p) { pthread_mutex_unlock(&p->mu); }
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
resource counter_state(p: struct counter*) {
    field value: uint32;
    owns p->value;
    fact p->value == value;
}
verifying "missing_state.c";
void release(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    consumes guard: mutex_guard(&p->mu);
} by {
    step();
    step();
    close();
}
```

```expect
fail: unsupported typed mutex helper: requires one matching named protected state transfer
```
