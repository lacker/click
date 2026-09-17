# A sidecar selects the user-space C target

A `target` directive picks the C implementation target the sidecar's sources
are preprocessed and verified under. The user-space target accepts the modeled
`<stddef.h>`, whose `NULL` is the null pointer constant, and the
declaration-only `<pthread.h>`. Including that header declares
`pthread_create` and `pthread_join`; it states no pthread contract and models
no concurrency.

```c filename=null_pointer.c
#include <stddef.h>
#include <pthread.h>

int32_t is_null(int32_t* p) {
    return p == NULL;
}
```

```click
target "x86_64-linux-userspace";
verifying "null_pointer.c";

int32 is_null(int32* p) {
    requires p == 0;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
