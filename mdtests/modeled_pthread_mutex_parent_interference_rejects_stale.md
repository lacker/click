# Shared parent writes do not survive worker interference

The parent writes under the lock, releases, reacquires, and joins the worker.
Each unlocked interval permits interference; join must not restore a saved value.

```c filename=modeled_pthread_mutex_parent_interference.c
#include <pthread.h>
#include <stddef.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
void *worker(void *argument) {
    struct counter *counter = argument;
    pthread_mutex_lock(&counter->mu);
    counter->value = counter->value + 1u;
    pthread_mutex_unlock(&counter->mu);
    return NULL;
}
unsigned int run(struct counter *counter) {
    pthread_t thread;
    pthread_mutex_init(&counter->mu, NULL);
    if (pthread_create(&thread, NULL, worker, counter) != 0) {
        pthread_mutex_destroy(&counter->mu);
        return counter->value;
    }
    pthread_mutex_lock(&counter->mu);
    counter->value = 99u;
    pthread_mutex_unlock(&counter->mu);
    pthread_mutex_lock(&counter->mu);
    counter->value = counter->value + 1u;
    pthread_mutex_unlock(&counter->mu);
    pthread_join(thread, NULL);
    pthread_mutex_destroy(&counter->mu);
    return counter->value;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "modeled_pthread_mutex_parent_interference.c";
resource counter_state(counter: struct counter*) {
    field value: uint32;
    owns counter->value;
    fact counter->value == value;
}
void* worker(void* argument) {
    owns access: mutex_use(&(argument as (struct counter *))->mu, counter_state(argument as (struct counter *)));
    ensures result == 0;
} by {
    step();
    step();
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    unfold(state);
    step();
    let restored = fold(counter_state(counter), { value: counter->value });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
uint32 run(struct counter* counter) {
    owns counter->mu;
    requires aligned(&counter->mu, 8);
    owns initial: counter_state(counter);
    requires initial.value == 100;
    ensures result == 100;
} by {
    step();
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: initial });
    step();
    branch {
        true => {
            step(pthread_mutex_destroy, { lifetime: lifetime });
            let { value: observed } = unfold(initial);
            step();
            let initial = fold(counter_state(counter), { value: observed });
            close();
        }
        false => {}
    }
    step();
    unfold(initial);
    step();
    let initial = fold(counter_state(counter), { value: counter->value });
    step();
    step();
    unfold(initial);
    step();
    let initial = fold(counter_state(counter), { value: counter->value });
    step();
    step();
    step(pthread_mutex_destroy, { lifetime: lifetime });
    let { value: final_observed } = unfold(initial);
    step();
    let initial = fold(counter_state(counter), { value: final_observed });
    close();
}
```

```expect
fail: ensures result == 100
```
