# The creation-time total is stale after locked workers join

Both workers have joined, so both deaths are applied. The total from before
the workers ran is no longer current.

```c filename=authority_mutex_locked_workers_stale_rejected.c
#include <pthread.h>
#include <stddef.h>
struct object { pthread_mutex_t mu; int refs; };
void *release(void *argument) {
    struct object *obj = argument;
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs - 1;
    pthread_mutex_unlock(&obj->mu);
    return NULL;
}
int run(void) {
    pthread_t a;
    pthread_t b;
    struct object *obj = malloc(sizeof(struct object));
    if (obj == 0) return -1;
    obj->refs = 2;
    pthread_mutex_init(&obj->mu, 0);
    if (pthread_create(&a, NULL, release, obj) != 0) {
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    if (pthread_create(&b, NULL, release, obj) != 0) {
        pthread_join(a, NULL);
        pthread_mutex_destroy(&obj->mu);
        free(obj);
        return 0;
    }
    pthread_join(a, NULL);
    pthread_join(b, NULL);
    pthread_mutex_destroy(&obj->mu);
    free(obj);
    return 1;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_workers_stale_rejected.c";
authorized resource reference(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
void* release(void* argument) {
    owns access: mutex_use(&(argument as (struct object *))->mu, control(argument as (struct object *)));
    consumes reference(argument as (struct object *));
} by {
    step();
    step();
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
    ensures to_integer(result) == -1 or result == 0 or result == 1;
} by {
    step();
    step();
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    step();
    fold(authority(reference(obj)));
    fold(reference(obj));
    fold(reference(obj));
    let control = fold(control(obj), { refs: 2 });
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: control });
    step();
    branch {
        true => {
            step(pthread_mutex_destroy, { lifetime: lifetime });
            unfold(control);
            unfold(reference(obj));
            unfold(reference(obj));
            have count(reference(obj)) == 0 by close();
            unfold(authority(reference(obj)));
            step();
            step();
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            step(pthread_mutex_destroy, { lifetime: lifetime });
            unfold(control);
            unfold(reference(obj));
            have count(reference(obj)) == 0 by close();
            unfold(authority(reference(obj)));
            step();
            step();
            close();
        }
        false => {}
    }
    step();
    step();
    step(pthread_mutex_destroy, { lifetime: lifetime });
    unfold(control);
    have count(reference(obj)) == 2 by close();
    unfold(authority(reference(obj)));
    step();
    step();
    close();
}
```

```expect
fail: could not establish `to_integer(count(reference(obj))) == 2`
```
