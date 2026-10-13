# An acquiring helper needs use of the mutex that holds the control

The control is deposited in `obj->mu`, and `obj->other` is an empty mutex.
Its lifetime authority cannot supply the acquiring helper's typed use of
`obj->mu`.

```c filename=authority_mutex_control_helper_wrong_mutex_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; pthread_mutex_t other; int refs; };
void acquire(struct object *obj) { pthread_mutex_lock(&obj->mu); }
void release(struct object *obj) { pthread_mutex_unlock(&obj->mu); }
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    pthread_mutex_init(&obj->other, 0);
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
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_control_helper_wrong_mutex_rejected.c";
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
    let { guard: acquired, state: state } = step(pthread_mutex_lock(&obj->mu), { access: access });
    step();
    simp();
}

void release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes guard: mutex_guard(&obj->mu);
    consumes state: control(obj);
} by {
    step(pthread_mutex_unlock(&obj->mu), { access: access, guard: guard, state: state });
    step();
    simp();
}

int32 run() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    let control = fold(control(obj), { refs: 0 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    let { lifetime: other } = step(pthread_mutex_init(&obj->other, 0), {});
    let { guard: first, state: entered } = step(acquire(obj), { access: other });
    step();
    simp();
}
```

```expect
fail: Requires owns mutex_use(&obj->mu, control(obj))
```
