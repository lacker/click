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
fail: system header `<stdio.h>` is not supported
```
