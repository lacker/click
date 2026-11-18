# Unknown system headers remain unsupported

```c filename=main.c
#include <assert.h>

int32 run() {
    return 0;
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 0;
}
```

```expect
fail: system header `<assert.h>` is not supported for x86_64-unknown-linux-gnu (userspace); the modeled headers for x86_64-unknown-linux-gnu (userspace) are <inttypes.h>, <limits.h>, <pthread.h>, <stdarg.h>, <stdatomic.h>, <stdbool.h>, <stddef.h>, <stdint.h>, <stdio.h>, <stdlib.h>, <string.h>, <sys/types.h> (see docs/reference/language/c.md#system-headers)
```
