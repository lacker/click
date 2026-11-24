# Locking a different mutex does not return the control

The control is deposited in `obj->mu`. The C program updates the counter
while holding `obj->other`, an empty mutex. That acquisition returns no
control, so the proof cannot open it.

```c filename=authority_mutex_control_wrong_mutex_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; pthread_mutex_t other; int refs; };
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    pthread_mutex_init(&obj->other, 0);
    pthread_mutex_lock(&obj->other);
    obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->other);
    pthread_mutex_destroy(&obj->other);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_control_wrong_mutex_rejected.c";
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
    let { lifetime: other } = step(pthread_mutex_init);
    step();
    unfold(control);
    step();
    step();
    close();
}
```

```expect
fail: resource instance is not owned
```
