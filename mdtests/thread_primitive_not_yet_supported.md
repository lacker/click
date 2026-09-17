# A thread primitive call reports that its semantics are not available yet

Under the `x86_64-linux-userspace` target, Click recognizes the modeled
`<pthread.h>` declarations of `pthread_create` and `pthread_join` as thread
primitives: a call to one means a checked kernel transition selected by the
declaration's identity, not a user-written contract. Those transitions are not
implemented yet, so a call fails promptly and names the primitive. It must not
fall through to the ordinary opaque-contract path, which would report a
missing or unsupported contract and invite someone to supply one.

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
fail: the thread primitive `pthread_join` is not yet supported
```
