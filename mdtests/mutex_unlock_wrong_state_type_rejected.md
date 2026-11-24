# Unlock names the state type it was given

Unlocking restores the protected type's state. Selecting a resource of
another type is refused, naming both the required and the selected type.

```c filename=mutex_unlock_wrong_state_type_rejected.c
#include <pthread.h>
struct pair { pthread_mutex_t mu; int a; int b; };
void copy_across(struct pair *p) {
    pthread_mutex_lock(&p->mu);
    p->b = p->a;
    pthread_mutex_unlock(&p->mu);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_unlock_wrong_state_type_rejected.c";
resource cell(p: struct pair*) {
    field v: int32;
    owns p->b;
    fact p->b == v;
}
resource pair_state(p: struct pair*) {
    field a: int32;
    field b: int32;
    owns p->a;
    owns second: cell(p);
    fact p->a == a;
    fact second.v == b;
}
void copy_across(struct pair *p) {
    owns access: mutex_use(&p->mu, pair_state(p));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    let { a: a, b: b, second: second } = unfold(state);
    unfold(second);
    step();
    let copied = fold(cell(p), { v: p->b });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: copied });
    step();
    close();
}
```

```expect
fail: Requires owns pair_state(p); the selected state is owns cell(p)
```
