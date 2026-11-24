# A fold names the child it does not supply

Folding a resource with a named child must supply that child in its child
map. The refusal names the child.

```c filename=named_child_fold_without_child_rejected.c
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
verifying "named_child_fold_without_child_rejected.c";
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
    let restored = fold(pair_state(p), { a: p->a, b: p->b });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
```

```expect
fail: fold of `pair_state` must supply its named child `second` in its input map
```
