# Unlock requires the mutex invariant folded

```c filename=guarded_resource_unlock_unfolded_rejected.c
#include <pthread.h>
struct cell { pthread_mutex_t mu; int value; };
void wrong(struct cell *cell) {
    pthread_mutex_init(&cell->mu, 0);
    pthread_mutex_lock(&cell->mu);
    pthread_mutex_unlock(&cell->mu);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource cell_state(cell: struct cell*) {
    field value: int32;
    guarded_by cell->mu;
    owns cell->value;
    fact cell->value == value;
}
verifying "guarded_resource_unlock_unfolded_rejected.c";
void wrong(struct cell *cell) {
    owns state: cell_state(cell);
} by {
    step(pthread_mutex_init(&cell->mu, 0), { invariant: state });
    step();
    unfold(state);
    step();
}
```

```expect
fail: mutex invariant must be folded before unlock
```
