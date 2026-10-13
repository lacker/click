# Abstract guard contracts need lifecycle support before retiring allocations

The allocator comes from Click's built-in `<stdlib.h>` and the mutex from its
built-in `<pthread.h>`.


The helper must prove its allocation is separate from the input mutex's
reserved storage. A guard alone does not justify freeing a possibly overlapping
allocation.

```c filename=mutex_storage_abstract_retirement.c
#include <pthread.h>
#include <stdlib.h>
struct holder { pthread_mutex_t mu; };
void release_other(struct holder *holder, int *data) {
    free(data);
}
```

```click
target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "mutex_storage_abstract_retirement.c";
void release_other(struct holder *holder, int32 *data) {
    requires data != 0;
    owns mutex_guard(&holder->mu);
    consumes allocation(data, 4);
    consumes data[0..1];
} by {
    execute();
    simp();
}
```

```expect
fail: Requires separate(data[0], *holder)
```
