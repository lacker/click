# Unknown system headers remain unsupported

```c filename=main.c
#include <stdio.h>

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
fail: system header `<stdio.h>` is not supported for x86_64-linux-userspace; the modeled headers for x86_64-linux-userspace are <inttypes.h>, <limits.h>, <pthread.h>, <stdatomic.h>, <stdbool.h>, <stddef.h>, <stdint.h>, <stdlib.h>, <string.h> (see docs/reference/language/c.md#system-headers)
```
