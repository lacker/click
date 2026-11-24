# A locked exchange must spend the member it declares consumed

This retain declares that it turns a permit into a reference, but its proof
creates the reference without spending the permit. The control ties its
`slack` field to the permit count, so the restored control's count fact
cannot be established and the unlock never happens.

```c filename=authority_mutex_locked_exchange_unspent_rejected.c
#include <pthread.h>
#include <stddef.h>

struct object {
    pthread_mutex_t mu;
    int refs;
};

void object_retain(struct object *obj) {
    pthread_mutex_lock(&obj->mu);
    obj->refs = obj->refs + 1;
    pthread_mutex_unlock(&obj->mu);
}
```

```click
import click::integer;

target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "authority_mutex_locked_exchange_unspent_rejected.c";
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
void object_retain(struct object *obj) {
    owns access: mutex_use(&obj->mu, control(obj));
    consumes permit(obj);
    produces reference(obj);
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    let { refs: refs, slack: slack } = unfold(state);
    have count(permit(obj)) >= 1 by close();
    have slack == count(permit(obj)) by close();
    have 1 <= slack by close();
    have to_integer(1) <= to_integer(slack);
    have to_integer(refs) + to_integer(slack) == 3 by close();
    have to_integer(refs) <= to_integer(2) by close() using {
        to_integer(refs) + to_integer(slack) == 3;
        to_integer(1) <= to_integer(slack);
    };
    have refs <= 2;
    have defined(refs + 1) by close();
    have defined(slack - 1) by close();
    have to_integer(refs + 1) == to_integer(refs) + to_integer(1);
    have to_integer(slack - 1) == to_integer(slack) - to_integer(1);
    have to_integer(refs + 1) + to_integer(slack - 1) == 3 by close() using {
        to_integer(refs + 1) == to_integer(refs) + to_integer(1);
        to_integer(slack - 1) == to_integer(slack) - to_integer(1);
        to_integer(refs) + to_integer(slack) == 3;
    };
    have obj->refs == refs by close();
    fold(reference(obj));
    have obj->refs <= 2 by close();
    step();
    let restored = fold(control(obj), { refs: refs + 1, slack: slack - 1 });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
```

```expect
fail: unproved obligation: `to_integer(((slack - 1) as int32)) == to_integer(count(permit(obj)))`
```
