# A resource published to another mutex cannot return to its owner

Without a mutex annotation, initialization associates a protected resource
with the mutex it initializes, so depositing `cell_state` in `cell->other` is
an ordinary publication. The contract still promises to return the state,
and the function ends with it held by a live mutex. The companion
`mutex_association_wrong_mutex_rejected.md` checks that a typed use of one
mutex cannot acquire a resource deposited in another.

```c filename=guarded_resource_wrong_mutex_rejected.c
#include <pthread.h>
struct cell { pthread_mutex_t guard; pthread_mutex_t other; int value; };
void wrong(struct cell *cell) { pthread_mutex_init(&cell->other, 0); }
```

```click
target "x86_64-unknown-linux-gnu";
runtime "modeled-pthread";
resource cell_state(cell: struct cell*) {
    field value: int32;
    owns cell->value;
    fact cell->value == value;
}
verifying "guarded_resource_wrong_mutex_rejected.c";
void wrong(struct cell *cell) {
    owns cell->other;
    requires aligned(&cell->other, 8);
    owns state: cell_state(cell);
} by {
    let { lifetime: mutex_lifetime } = step(pthread_mutex_init, { state: state });
    step();
    close();
}
```

```expect
fail: a function cannot return with a held mutex or an unpublished guarded resource
```
