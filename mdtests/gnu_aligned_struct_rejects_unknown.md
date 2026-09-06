# Unknown GNU struct attributes are rejected

Layout-affecting attributes need an explicit model; they must not be silently
dropped from imported declarations.

```c filename=bad.h
struct packed_node {
    int32 value;
} __attribute__((packed));
```

```c filename=main.c
#include "bad.h"

int32 run() {
    return 1;
}
```

```click
verifying "main.c";
```

```expect
fail:unsupported GNU struct attribute `packed`
```
