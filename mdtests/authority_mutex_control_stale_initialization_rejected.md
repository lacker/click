# An earlier initialization cannot reclaim a redeposited control

The control is deposited, recovered by destruction, and deposited again by a
second initialization of the same mutex. The first initialization's lifetime
authority is stale: it cannot destroy the second initialization.

```c filename=authority_mutex_control_stale_initialization_rejected.c
#include <pthread.h>
struct object { pthread_mutex_t mu; int refs; };
int run(void) {
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 0;
    pthread_mutex_init(&obj->mu, 0);
    pthread_mutex_destroy(&obj->mu);
    pthread_mutex_init(&obj->mu, 0);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 0;
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "authority_mutex_control_stale_initialization_rejected.c";
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
    branch then { step(); simp(); } else {}
    step();
    fold(authority(reference(obj)));
    let control = fold(control(obj), { refs: 0 });
    let { lifetime: lifetime } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    let { lifetime: second } = step(pthread_mutex_init(&obj->mu, 0), { state: control });
    step(pthread_mutex_destroy(&obj->mu), { lifetime: lifetime });
    unfold(control);
    unfold(authority(reference(obj)));
    step();
    step();
    simp();
}
```

```expect
fail: Requires owns mutex_live(&obj->mu)
```
