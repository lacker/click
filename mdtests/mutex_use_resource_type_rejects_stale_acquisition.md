# Each acquisition observes the protected state afresh

```c filename=mutex_use_resource_type_reacquire.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
int unchanged(struct counter *counter) {
    unsigned int first;
    unsigned int second;
    pthread_mutex_lock(&counter->mu);
    first = counter->value;
    pthread_mutex_unlock(&counter->mu);
    pthread_mutex_lock(&counter->mu);
    second = counter->value;
    pthread_mutex_unlock(&counter->mu);
    return first == second;
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
verifying "mutex_use_resource_type_reacquire.c";
int32 unchanged(struct counter *counter) {
    owns access: mutex_use(&counter->mu, counter_state(counter));
    ensures result == 1;
} by {
    step();
    step();
    let { guard: first_guard, state: first_state } = step(pthread_mutex_lock, { access: access });
    unfold(first_state);
    step();
    let first_restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock, { access: access, guard: first_guard, state: first_restored });
    let { guard: second_guard, state: second_state } = step(pthread_mutex_lock, { access: access });
    unfold(second_state);
    step();
    let second_restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock, { access: access, guard: second_guard, state: second_restored });
    step();
    close();
}
```

```expect
fail: ensures result == 1
```
