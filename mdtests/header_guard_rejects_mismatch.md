# Header guards must frame the complete header

```c filename=bad.h
#ifndef BAD_H
#define OTHER_H
typedef int32 value_t;
#endif
```

```c filename=main.c
#include "bad.h"

int32 run() {
    return sizeof(value_t);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 4;
}
```

```expect
fail: only whole-header guards are supported
```
