# mutex guard rejects quantities

The guard folds into an ordinary exclusive resource and must be recovered
before unlock. The protected counter assertion remains a separate resource.
This uses the unchanged C from the guarded mutex flow fixture.

```c filename=guarded_resource_mutex_flow.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; int value; };

int read_counter(struct counter *counter) {
    int value;
    pthread_mutex_init(&counter->mu, 0);
    pthread_mutex_lock(&counter->mu);
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
    owns 2 of mutex_guard(&counter->mu);
}

resource counter_state(counter: struct counter*) {
    field value: int32;
    owns counter->value;
    fact counter->value == value;
}

verifying "guarded_resource_mutex_flow.c";

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
fail: `mutex_guard` is exclusive and not countable
```
