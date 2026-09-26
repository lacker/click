# A guard contract cannot consume an opaque guard

A preserving contract frames the wrapper and its acquisition. The helper
receives no permission to change the mutex protocol.

```c filename=guarded_resource_mutex_flow.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

void keep(struct counter *counter) {}

int read_counter(struct counter *counter) {
    int value;
    pthread_mutex_init(&counter->mu, 0);
    pthread_mutex_lock(&counter->mu);
    keep(counter);
    value = counter->value;
    pthread_mutex_unlock(&counter->mu);
    pthread_mutex_destroy(&counter->mu);
    return value;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";

resource holding(counter: struct counter*) {
    field tag: int32;
    owns mutex_guard(&counter->mu);
}

resource counter_state(counter: struct counter*) {
    field value: int32;
    guarded_by counter->mu;
    owns counter->value;
    fact counter->value == value;
}

verifying "guarded_resource_mutex_flow.c";

void keep(struct counter *counter) {
    consumes h: holding(counter);
} by {
    execute();
    simp();
}

int32 read_counter(struct counter *counter) {
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    step();
    step(pthread_mutex_init(&counter->mu, 0), { invariant: state });
    step();
    let held = fold(holding(counter), { tag: 0 });
    step(keep(counter), { h: held });
    unfold(held);
    unfold(state);
    step();
    fold(state);
    step();
    step();
    step();
    simp();
}
```

```expect
fail: guard-bearing contracts currently require preserving owned instance inputs
```
