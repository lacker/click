# A releaser cannot free the shared object

Releasing a reference under the mutex leaves the object shared: the owner and
the other users may still hold it, and the mutex inside it is live. A releaser
holding only a use share owns neither the allocation nor the mutex lifetime,
so freeing the object after its release is refused.

```c filename=refcount_releaser_cannot_free_shared_object.c
#include <pthread.h>
#include <stddef.h>

struct object {
    pthread_mutex_t mu;
    int refs;
};

void object_release(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs - 1;
    pthread_mutex_unlock(&obj->mu);
}

void release_and_free(struct object *obj) {
    object_release(obj);
    free(obj);
}
```

```click
import click::integer;

target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
authorized resource reference(obj: struct object*) {}
authorized resource permit(obj: struct object*) {}
resource control(obj: struct object*) {
    field refs: int32;
    field slack: int32;
    owns obj->refs;
    owns authority(reference(obj));
    owns authority(permit(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
    fact slack == count(permit(obj));
    fact to_integer(refs) + to_integer(slack) == 3;
}

verifying "refcount_releaser_cannot_free_shared_object.c";

void object_release(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes reference(obj);
    produces permit(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    let { refs: refs, slack: slack } = unfold(state);
    have count(reference(obj)) >= 1;
    have refs == count(reference(obj));
    have 1 <= refs;
    have to_integer(1) <= to_integer(refs);
    have to_integer(refs) + to_integer(slack) == 3;
    have to_integer(slack) <= to_integer(2) by close() using {
        to_integer(refs) + to_integer(slack) == 3;
        to_integer(1) <= to_integer(refs);
    };
    have slack <= 2;
    have defined(refs - 1);
    have defined(slack + 1);
    have to_integer(refs - 1) == to_integer(refs) - to_integer(1);
    have to_integer(slack + 1) == to_integer(slack) + to_integer(1);
    have to_integer(refs - 1) + to_integer(slack + 1) == 3 by close() using {
        to_integer(refs - 1) == to_integer(refs) - to_integer(1);
        to_integer(slack + 1) == to_integer(slack) + to_integer(1);
        to_integer(refs) + to_integer(slack) == 3;
    };
    have obj->refs == refs;
    unfold(reference(obj));
    fold(permit(obj));
    have obj->refs >= 1;
    step();
    let restored = fold(control(obj), { refs: refs - 1, slack: slack + 1 });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}

void release_and_free(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes reference(obj);
    produces permit(obj);
} by {
    step(object_release, { access: access });
}
```

```expect
fail: cannot free a pointer that is not a live heap allocation
```
