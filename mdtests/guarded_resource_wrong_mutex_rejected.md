# A guarded resource cannot be published to another mutex

```c filename=guarded_resource_wrong_mutex_rejected.c
#include <pthread.h>
struct cell { pthread_mutex_t guard; pthread_mutex_t other; int value; };
void wrong(struct cell *cell) { pthread_mutex_init(&cell->other, 0); }
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
resource cell_state(cell: struct cell*) {
    field value: int32;
    guarded_by cell->guard;
    owns cell->value;
    fact cell->value == value;
}
verifying "guarded_resource_wrong_mutex_rejected.c";
void wrong(struct cell *cell) {
    owns state: cell_state(cell);
} by {
    step(pthread_mutex_init(&cell->other, 0), { invariant: state });
}
```

```expect
fail: selected resource is guarded by a different mutex
```
