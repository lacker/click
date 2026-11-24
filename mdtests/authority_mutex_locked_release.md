# A locked helper spends its member under the acquired authority

`release` locks the object's mutex, opens the acquired control, spends the
member its caller lends, decrements the counter, and restores the control
before unlocking. The acquisition enters the population with a fresh total
bounded below by the lent member, so the helper's count facts relate only to
that acquisition. Its contract declares the death with `consumes`, and the
helper's checked spend matches it. The creator applies that death to the
population held by the mutex and, after destruction, observes zero and
retires the authority.

```c filename=authority_mutex_locked_release.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
void release(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs - 1;
    pthread_mutex_unlock(&obj->mu);
}
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 1;
    pthread_mutex_init(&obj->mu, 0);
    release(obj);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_release.c";
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
    unfold(reference(obj));
    step();
    let restored = fold(control(obj), { refs: obj->refs });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
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
    fold(reference(obj));
    let control = fold(control(obj), { refs: 1 });
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: control });
    step(release, { access: lifetime });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    unfold(control);
    have count(reference(obj)) == 0;
    unfold(authority(reference(obj)));
    step();
    step();
    close();
}
```

```expect
pass
```
