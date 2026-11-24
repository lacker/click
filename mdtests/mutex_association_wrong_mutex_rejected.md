# A typed use of one mutex cannot acquire a resource deposited in another

Initialization associates `cell_state` with `cell->other`. The helper's
typed use names `cell->guard`, so the lifetime authority of `cell->other`
cannot supply it, and the call is refused. The C would lock an
uninitialized mutex.

```c filename=mutex_association_wrong_mutex_rejected.c
#include <pthread.h>
struct cell { pthread_mutex_t guard; pthread_mutex_t other; int value; };
void touch(struct cell *cell) {
    pthread_mutex_lock(&cell->guard);
    cell->value = 1;
    pthread_mutex_unlock(&cell->guard);
}
void run(struct cell *cell) {
    pthread_mutex_init(&cell->other, 0);
    touch(cell);
    pthread_mutex_destroy(&cell->other);
}
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
resource cell_state(cell: struct cell*) {
    field value: int32;
    owns cell->value;
    fact cell->value == value;
}
verifying "mutex_association_wrong_mutex_rejected.c";
void touch(struct cell *cell) {
    owns access: mutex_use(&cell->guard, cell_state(cell));
} by {
    let { guard: guard, state: state } = step(pthread_mutex_lock, { access: access });
    unfold(state);
    step();
    let restored = fold(cell_state(cell), { value: cell->value });
    step(pthread_mutex_unlock, { access: access, guard: guard, state: restored });
    step();
    close();
}
void run(struct cell *cell) {
    owns cell->other;
    requires aligned(&cell->other, 8);
    owns initial: cell_state(cell);
} by {
    let { lifetime: lifetime } = step(pthread_mutex_init, { state: initial });
    step(touch, { access: lifetime });
    step(pthread_mutex_destroy, { lifetime: lifetime });
    step();
    close();
}
```

```expect
fail: Requires owns mutex_use(&cell->guard, cell_state(cell))
```
