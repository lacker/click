# A folded guard must be exposed before a direct guard call

A preserving contract frames the wrapper and its acquisition. The helper
receives no permission to change the mutex protocol.

```c filename=guarded_resource_mutex_flow.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

int read_locked(struct counter *counter) { return counter->value; }

int read_counter(struct counter *counter) {
    int value;
    pthread_mutex_init(&counter->mu, 0);
    pthread_mutex_lock(&counter->mu);
    value = read_locked(counter);
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

int32 read_locked(struct counter *counter) {
    owns mutex_guard(&counter->mu);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    have held(&counter->mu) by simp;
    unfold(state);
    execute();
    fold(state);
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
    step(read_locked(counter), { state: state });
    unfold(held);
    step();
    step();
    step();
    simp();
}
```

```expect
fail: Requires owns mutex_guard(&counter->mu)
```
