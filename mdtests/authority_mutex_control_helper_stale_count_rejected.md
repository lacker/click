# A count from before an earlier critical section is historical

The first critical section creates a member. After the control returns
through the acquiring helper again, the current count is one; the zero
observed before the first acquisition cannot be claimed.

```c filename=authority_mutex_control_helper_stale_count_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void acquire(struct object *obj) { pthread_mutex_lock(&obj->mu); }
void release(struct object *obj) { pthread_mutex_unlock(&obj->mu); }
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    acquire(obj);
    obj->refs = obj->refs + 1;
    release(obj);
    acquire(obj);
    obj->refs = obj->refs - 1;
    release(obj);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_control_helper_stale_count_rejected.c";
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}

void acquire(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    produces guard: mutex_guard(&obj->mu);
    produces state: control(obj);
} by {
    let { guard: acquired, state: state } = step(pthread_mutex_lock, { access: access });
    step();
    close();
}

void release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes guard: mutex_guard(&obj->mu);
    consumes state: control(obj);
} by {
    step(pthread_mutex_unlock, { access: access, guard: guard, state: state });
    step();
    close();
}

int32 run() {
    ensures to_integer(result) == -1 or result == 0;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    step();
    fold(authority(reference(obj)));
    let control = fold(control(obj), { refs: 0 });
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: control });
    let { guard: first, state: entered } = step(acquire, { access: lifetime });
    unfold(entered);
    step();
    fold(reference(obj));
    let retained = fold(control(obj), { refs: 1 });
    step(release, { access: lifetime, guard: first, state: retained });
    let { guard: second, state: reentered } = step(acquire, { access: lifetime });
    unfold(reentered);
    have count(reference(obj)) == 0 by close();
    have count(reference(obj)) == 1 by close();
    unfold(reference(obj));
    step();
    let released = fold(control(obj), { refs: 0 });
    step(release, { access: lifetime, guard: second, state: released });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    unfold(released);
    unfold(authority(reference(obj)));
    step();
    step();
    close();
}
```

```expect
fail: could not establish `to_integer(count(reference(obj))) == 0`
```
