# A lifecycle name cannot select a later initialization at the same address

```c filename=mutex_lifetime_named_stale_runtime.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };
void reset(struct counter *counter) {
    pthread_mutex_init(&counter->mu, 0);
    pthread_mutex_destroy(&counter->mu);
    pthread_mutex_init(&counter->mu, 0);
    pthread_mutex_destroy(&counter->mu);
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
verifying "mutex_lifetime_named_stale_runtime.c";
void reset(struct counter *counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns state: counter_state(counter);
} by {
    let { lifetime: before } = step(pthread_mutex_init, { state: state });
    step(pthread_mutex_destroy, { lifetime: before });
    let { lifetime: after } = step(pthread_mutex_init, { state: state });
    step(pthread_mutex_destroy, { lifetime: before });
    step();
    close();
}
```

```expect
fail: Requires owns mutex_live(&counter->mu)
```
