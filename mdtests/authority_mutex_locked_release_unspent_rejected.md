# A locked helper cannot declare a death it does not perform

This `release` declares `consumes reference(obj)` but leaves the counter and
the population unchanged under the acquired authority. Its caller would apply
a death that never happened, so the helper's contract is refused.

```c filename=authority_mutex_locked_release_unspent_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void release(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs + 0;
    pthread_mutex_unlock(&obj->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_release_unspent_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes reference(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    unfold(state);
    step();
    let restored = fold(control(obj), { refs: obj->refs });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
```

```expect
fail: Requires consumes reference(obj)
```
