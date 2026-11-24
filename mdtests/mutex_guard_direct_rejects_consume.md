# Consuming a direct guard requires a releasing helper interface

This read-only helper has no preserved use permission and does not unlock.
It cannot discharge an acquisition by declaring the guard consumed.

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
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";

resource counter_state(counter: struct counter*) {
    field value: int32;
    owns counter->value;
    fact counter->value == value;
}

verifying "guarded_resource_mutex_flow.c";

int32 read_locked(struct counter *counter) {
    consumes mutex_guard(&counter->mu);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    have held(&counter->mu) by close();
    unfold(state);
    step_until(function.exit);
    fold(state);
    close();
}

int32 read_counter(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
    ensures result == state.value;
} by {
    step();
    let { lifetime: mutex_lifetime } = step(pthread_mutex_init, { state: state });
    step();
    step(read_locked, { state: state });
    step();
    step();
    step();
    close();
}
```

```expect
fail: unsupported mutex helper contract: requires one named preserved mutex_use and one produced or consumed guard
```
