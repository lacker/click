# Headers are declaration-only

```c filename=bad.h
int32 hidden() {
    return 1;
}
```

```c filename=main.c
#include "bad.h"

int32 run() {
    return hidden();
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 1;
}
```

```expect
fail: function definitions are not allowed in headers
```
