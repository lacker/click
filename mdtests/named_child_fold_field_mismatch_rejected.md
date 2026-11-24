# A fold names the child field that does not match

The parent's field `b` is tied to its child's field `v`. Folding with a
value for `b` the child does not hold is refused, naming that child field.

```c filename=named_child_fold_field_mismatch_rejected.c
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
verifying "named_child_fold_field_mismatch_rejected.c";
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
    let restored = fold(pair_state(p), { a: p->a, b: 7, second: copied });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
```

```expect
fail: child `second` field `v` is not proven equal to the value the proposed parent fields give it
```
