# Abstract guard contracts need lifecycle support before retiring allocations

This C0 fixture uses the allocator builtins directly; the unsupported
`stdlib.h` include is omitted. The modeled pthread declarations are retained.


Even when the allocation might be unrelated, the current preserving contract
has no checked lifetime interface to establish that distinction. This is an
explicit verifier limitation, not a missing ownership claim or a C bug.

```c filename=mutex_storage_abstract_retirement.c
#include <pthread.h>
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
fail: Click does not yet support freeing or reallocating storage in a preserving guard contract
```
