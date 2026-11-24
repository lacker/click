# An external credit does not establish a closed total

The worker owns one external credit, but its contract does not relate that credit to the number already protected by the mutex. Restoring credits <= 2 after a deposit must fail.

```c filename=mutex_resource_quantity_requires_conservation.c
#include <pthread.h>
#include <stddef.h>

struct mutex_counter {
    pthread_mutex_t mutex;
    unsigned int value;
};

void *increment_counter(void *argument) {
    struct mutex_counter *counter = argument;
    (void)pthread_mutex_lock(&counter->mutex);
    counter->value = counter->value + 1u;
    (void)pthread_mutex_unlock(&counter->mutex);
    return NULL;
}

int increment_twice(struct mutex_counter *counter) {
    pthread_t first;
    pthread_t second;

    counter->value = 0u;
    if (pthread_mutex_init(&counter->mutex, NULL) != 0) return 0;
    if (pthread_create(&first, NULL, increment_counter, counter) != 0) {
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }
    if (pthread_create(&second, NULL, increment_counter, counter) != 0) {
        (void)pthread_join(first, NULL);
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }

    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    (void)pthread_mutex_destroy(&counter->mutex);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_resource_quantity_requires_conservation.c";
abstract resource increment_credit(counter: struct mutex_counter*);
resource counter_state(counter: struct mutex_counter*) {
    field value: uint32;
    field credits: int32;
    owns counter->value;
    owns credits of increment_credit(counter);
    fact credits >= 0;
    fact credits <= 2;
    fact counter->value == value;
    fact value == credits;
}
void* increment_counter(void* argument) {
    owns access: mutex_use(&(argument as (struct mutex_counter *))->mutex, counter_state(argument as (struct mutex_counter *)));
    consumes increment_credit(argument as (struct mutex_counter *));
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    let { credits: n } = unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value, credits: n + 1 });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
```

```expect
fail: unproved obligation: `((n + 1) as int32) <= 2`
```
