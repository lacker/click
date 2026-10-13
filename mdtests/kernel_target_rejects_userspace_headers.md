# The kernel target rejects user-space system headers

The `x86_64-linux-kernel` target has no `<stddef.h>` or `<pthread.h>` model, so
this source is rejected under it. The same source verifies under
`target "x86_64-linux-userspace";` (`mdtests/userspace_target_directive.md`).

```c filename=null_pointer.c
#include <stddef.h>
#include <pthread.h>

int32_t is_null(int32_t* p) {
    return p == NULL;
}
```

```click
target "x86_64-linux-kernel";
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
