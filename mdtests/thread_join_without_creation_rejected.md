# A join needs a completion right, not a handle value

A `pthread_t` value alone is no authority to join: only a successful
`pthread_create` on the same path mints the linear right a join consumes.
Here the handle is a parameter the caller never created, so the join is
refused where it is written.

```c filename=join_once.c
#include <pthread.h>

int join_once(pthread_t handle) {
    return pthread_join(handle, 0);
}
```

```click
target "x86_64-linux-userspace";
verifying "join_once.c";

int32 join_once(uint64 handle) {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: the handle's bits carry no authority
```
