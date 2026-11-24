# A release helper's mutation cannot revive an earlier payload observation

The releasing helper changes the value before depositing a replacement state.
The caller must not learn that a later acquisition has the earlier value.

```c filename=stale_helper_payload.c
#include <pthread.h>
struct counter { pthread_mutex_t mu; unsigned int value; };
void acquire(struct counter *p) { pthread_mutex_lock(&p->mu); }
void reset_release(struct counter *p) {
    p->value = 7u;
    pthread_mutex_unlock(&p->mu);
}
int compare(struct counter *p) {
    acquire(p);
    unsigned int saved = p->value;
    reset_release(p);
    acquire(p);
    unsigned int after = p->value;
    reset_release(p);
    return after == saved;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
resource counter_state(p: struct counter*) {
    field value: uint32;
    owns p->value;
    fact p->value == value;
}
verifying "stale_helper_payload.c";
void acquire(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    produces guard: mutex_guard(&p->mu);
    produces state: counter_state(p);
} by {
    let { guard: acquired, state: state } = step(pthread_mutex_lock, { access: access });
    step();
    close();
}
void reset_release(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    consumes guard: mutex_guard(&p->mu);
    consumes state: counter_state(p);
} by {
    unfold(state);
    step();
    let restored = fold(counter_state(p), { value: p->value });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
int32 compare(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    ensures result == 1;
} by {
    let { guard: first_guard, state: first_state } = step(acquire, { access: access });
    unfold(first_state);
    step();
    step();
    let restored_first = fold(counter_state(p), { value: p->value });
    step(reset_release, { access: access, guard: first_guard, state: restored_first });
    let { guard: second_guard, state: second_state } = step(acquire, { access: access });
    unfold(second_state);
    step();
    step();
    let restored_second = fold(counter_state(p), { value: p->value });
    step(reset_release, { access: access, guard: second_guard, state: restored_second });
    step();
    close();
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 1
```
