# A releasing helper requires the restored control

The second critical section opens the control and spends the member, but
the proof calls the releasing helper with the opened control instead of a
restored replacement. The helper's `consumes state` clause is not met.

```c filename=authority_mutex_control_helper_missing_state_rejected.c
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
verifying "authority_mutex_control_helper_missing_state_rejected.c";
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
    ensures result == -1 or result == 0;
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
    unfold(reference(obj));
    step();
    step(release, { access: lifetime, guard: second, state: reentered });
    step();
    close();
}
```

```expect
fail: resource proof argument is not owned
```
