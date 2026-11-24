# Initialization without an annotation still checks the protected resource type

```c filename=mutex_use_resource_type.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
void increment(struct counter *counter) {
    pthread_mutex_lock(&counter->mu);
    counter->value = counter->value + 1u;
    pthread_mutex_unlock(&counter->mu);
}
void outer(struct counter *counter) { increment(counter); }
void run(struct counter *counter) {
    pthread_mutex_init(&counter->mu, 0);
    outer(counter);
    pthread_mutex_destroy(&counter->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
resource counter_state(counter: struct counter*) {
    field value: uint32;
    owns counter->value;
    fact counter->value == value;
}
resource other_state(counter: struct counter*) {
    field value: uint32;
}
verifying "mutex_use_resource_type.c";
void increment(struct counter *counter) {
    owns access: mutex_use(&counter->mu, counter_state(counter));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
void outer(struct counter *counter) {
    owns access: mutex_use(&counter->mu, other_state(counter));
} by {
    step(increment, { access: access });
    step();
    close();
}
void run(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns initial: counter_state(counter);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: initial });
    step(outer, { access: lifetime });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    step();
    close();
}
```

```expect
fail: Requires owns mutex_use(&counter->mu, counter_state(counter))
```
