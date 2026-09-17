# User-space system headers need the user-space target

The default `x86_64-linux-kernel` target has no `<stddef.h>` or `<pthread.h>`
model, so the same source is rejected until the sidecar selects the user-space
target with `target "x86_64-linux-userspace";`.

```c filename=null_pointer.c
#include <stddef.h>
#include <pthread.h>

int32_t is_null(int32_t* p) {
    return p == NULL;
}
```

```click
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
fail: system header `<stddef.h>` is not supported for x86_64-linux-kernel
```
