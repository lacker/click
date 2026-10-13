# Hosted library headers need the user-space target

`<string.h>` and `<stdlib.h>` are hosted C library headers. The Linux kernel
target refuses them, as it refuses `<stddef.h>` and `<pthread.h>`.

```c filename=kernel_stdlib.c
#include <stdlib.h>

int f(void) {
    return 0;
}
```

```click
target "x86_64-linux-kernel";
verifying "kernel_stdlib.c";

int f() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: system header `<stdlib.h>` is not supported for x86_64-linux-kernel
```
