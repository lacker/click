# Two workers release references under the mutex

Each worker borrows a typed `mutex_use` share and consumes one reference.
Its standalone proof locks the object, opens the acquired control, spends the
reference, decrements the counter, and restores the control before unlocking.
The authority stays in the mutex while both workers are outstanding, so
neither worker borrows it from the creator at create. Each join applies that
worker's checked death. After both joins and the destroy, the creator observes
zero, retires the population, and frees the object. A failed create spends the
creator's remaining reference itself.

```c filename=authority_mutex_locked_workers.c
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
verifying "authority_mutex_locked_workers.c";
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
    ensures result == -1 or result == 0 or result == 1;
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
            have count(reference(obj)) == 0;
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
            have count(reference(obj)) == 0;
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
