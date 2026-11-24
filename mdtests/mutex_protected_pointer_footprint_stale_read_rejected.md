# A released protected footprint reached through a pointer is forgotten

The protected control owns a pointer cell and, through a named child, the
memory it points to. The worker reads that memory in two critical sections.
Another thread may store between them, so the second read is not the first,
even though this worker never wrote it. Unlocking forgets the footprint the
worker held, found through the pointer value it held then.

```c filename=mutex_protected_pointer_footprint_stale_read_rejected.c
#include <pthread.h>
struct box { pthread_mutex_t mu; int *slot; };
int read_twice(struct box *b) {
    int first;
    int second;
    pthread_mutex_lock(&b->mu);
    first = *b->slot;
    pthread_mutex_unlock(&b->mu);
    pthread_mutex_lock(&b->mu);
    second = *b->slot;
    pthread_mutex_unlock(&b->mu);
    return first == second;
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
verifying "mutex_protected_pointer_footprint_stale_read_rejected.c";
resource target(q: int32*) {
    field v: int32;
    owns *q;
    fact *q == v;
}
resource box_state(b: struct box*) {
    field v: int32;
    owns b->slot;
    owns held: target(b->slot);
    fact held.v == v;
}
int32 read_twice(struct box *b) {
    owns access: mutex_use(&b->mu, box_state(b));
    ensures result == 1;
} by {
    step();
    step();
    let { guard: first_guard, state: first_state } = step(pthread_mutex_lock, { access: access });
    let { v: first_v, held: first_held } = unfold(first_state);
    unfold(first_held);
    have b->slot == at(statement(2).exit, b->slot) by { close(); }
    step();
    let first_target = fold(target(b->slot), { v: *b->slot });
    let first_restored = fold(box_state(b), { v: *b->slot, held: first_target });
    step(pthread_mutex_unlock, { access: access, guard: first_guard, state: first_restored });
    let { guard: second_guard, state: second_state } = step(pthread_mutex_lock, { access: access });
    let { v: second_v, held: second_held } = unfold(second_state);
    unfold(second_held);
    have b->slot == at(statement(5).exit, b->slot) by { close(); }
    step();
    let second_target = fold(target(b->slot), { v: *b->slot });
    let second_restored = fold(box_state(b), { v: *b->slot, held: second_target });
    step(pthread_mutex_unlock, { access: access, guard: second_guard, state: second_restored });
    step();
    close();
}
```

```expect
fail: `ensures result == 1` failed
```
