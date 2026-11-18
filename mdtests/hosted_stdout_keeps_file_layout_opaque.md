# The hosted stream handle confers no access to FILE layout

```c filename=opaque.c
#include <stdio.h>

int stream_size(void)
{
    return sizeof(FILE);
}
```

```click
verifying "opaque.c";

int32 stream_size() {
    ensures result > 0;
}
```

```expect
fail: unknown struct declaration
```
