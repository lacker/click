# A locked helper cannot hide a member birth from its caller

`bump` creates a member under the acquired authority and keeps the counter
equation, but its contract declares no `produces`. Its caller would keep a
total that misses the birth, so the undeclared change is refused.

```c filename=authority_mutex_locked_undeclared_birth_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void bump(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    if (obj->refs < 1000) obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_undeclared_birth_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void bump(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    unfold(state);
    if obj->refs < 1000 {
        fold(reference(obj));
        step();
        step();
        let grown = fold(control(obj), { refs: obj->refs });
        step(pthread_mutex_unlock, { access: access, guard: guard, state: grown });
        step();
        close();
    } else {
        step();
        step();
        let same = fold(control(obj), { refs: obj->refs });
        step(pthread_mutex_unlock, { access: access, guard: guard, state: same });
        step();
        close();
    }
}
```

```expect
fail: a change to reference(...) under the acquired authority must be declared by produces or consumes
```
