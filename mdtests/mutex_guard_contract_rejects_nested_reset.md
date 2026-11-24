# An opaque guard cannot hide an untracked nested protocol change

A preserving contract frames the wrapper and its acquisition. The helper
receives no permission to change the mutex protocol.

```c filename=guarded_resource_mutex_flow.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

void reset(struct counter *counter) { pthread_mutex_init(&counter->mu, 0); }
void keep(struct counter *counter) { reset(counter); }

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
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";

resource holding(counter: struct counter*) {
    field tag: int32;
    owns mutex_guard(&counter->mu);
}

resource counter_state(counter: struct counter*) {
    field value: int32;
    owns counter->value;
    fact counter->value == value;
}

verifying "guarded_resource_mutex_flow.c";

void reset(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    ensures 0 == 0;
}

void keep(struct counter *counter) {
    owns h: holding(counter);
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
    let held = fold(holding(counter), { tag: 0 });
    step(keep, { h: held });
    unfold(held);
    unfold(state);
    step();
    fold(state);
    step();
    step();
    step();
    close();
}
```

```expect
fail: missing resource fact `owns counter->mu`
```
