# An unbounded locked retain can overflow its counter

Without a stated cap, the control relates the counter only to the
reference count, which nothing bounds. The increment can overflow `int`, so
the plain `refs + 1` is refused. `examples/shared-refcount` bounds it with
retain permits.

```c filename=authority_mutex_locked_retain_without_cap_rejected.c
#include <pthread.h>
#include <stddef.h>

struct object {
    pthread_mutex_t mu;
    int refs;
};

void object_retain(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_retain_without_cap_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void object_retain(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    owns reference(obj);
    produces reference(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    let { refs: refs } = unfold(state);
    fold(reference(obj));
    step();
    let restored = fold(control(obj), { refs: refs + 1 });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
```

```expect
fail: signed overflow
```
