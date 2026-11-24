# A protected counter update without a member cannot restore the control

The C counter increases inside the critical section, but the proof creates
no member. The control's counter equation then fails, so it cannot be folded
again for unlock.

```c filename=authority_mutex_control_bad_increment_rejected.c
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
verifying "authority_mutex_control_bad_increment_rejected.c";
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
    let control = fold(control(obj), { refs: 1 });
    step();
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
fail: unproved obligation: `to_integer((1 as int32)) == to_integer(count(reference(obj)))`
```
