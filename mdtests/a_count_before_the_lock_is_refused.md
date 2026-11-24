# A count before the lock is refused

Before `release` locks the mutex, it holds only the borrowed
`mutex_use(&obj->mu, control(obj))`, which does not give it the population's
authority. Reading `count(reference(obj))` there is refused, even through
`at(...)`.

```c filename=a_count_before_the_lock_is_refused.c
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
verifying "a_count_before_the_lock_is_refused.c";
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
    have at(statement(0).entry, count(reference(obj))) >= 0;
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
fail: count(...) requires owning authority for that population
```
