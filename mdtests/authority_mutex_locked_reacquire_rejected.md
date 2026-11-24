# A standalone helper enters an acquired population at most once

Each typed lock in a helper's proof enters the control's population with a
fresh total. A second acquisition in the same proof would need a second fresh
total for a population the proof already accounts for, so it is refused
rather than allowed to reuse facts from the first critical section.

```c filename=authority_mutex_locked_reacquire_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void twice(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    pthread_mutex_unlock(&obj->mu);
    pthread_mutex_lock(&obj->mu);
    pthread_mutex_unlock(&obj->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_reacquire_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void twice(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
} by {
    let { guard: first, state: entered } = step(pthread_mutex_lock, { access: access });
    step(pthread_mutex_unlock, { access: access, guard: first, state: entered });
    let { guard: second, state: reentered } = step(pthread_mutex_lock, { access: access });
    step(pthread_mutex_unlock, { access: access, guard: second, state: reentered });
    step();
    close();
}
```

```expect
fail: acquire its control at most once
```
