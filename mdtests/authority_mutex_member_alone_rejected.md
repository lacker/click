# A member alone does not expose a mutex-held control

The critical section creates a member and the proof keeps it after unlock.
While the control sits in the mutex, that member grants no count
observation: the authority is inside the deposited control.

```c filename=authority_mutex_member_alone_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->mu);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_member_alone_rejected.c";
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
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
    step();
    unfold(control);
    step();
    fold(reference(obj));
    have count(reference(obj)) == 1 by close();
    let control = fold(control(obj), { refs: 1 });
    step();
    have count(reference(obj)) == 1 by close();
    step(pthread_mutex_destroy, { lifetime: lifetime });
    unfold(control);
    unfold(reference(obj));
    unfold(authority(reference(obj)));
    step();
    step();
    close();
}
```

```expect
fail: count(...) requires owning authority for that population
```
