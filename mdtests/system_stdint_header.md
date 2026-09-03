# The modeled stdint header supplies standard C0 type spellings

```c filename=include/types.h
#ifndef TYPES_H
#define TYPES_H
#include <stdint.h>

int32_t increment(uint8_t value);
#endif
```

```c filename=worker.c
#include "include/types.h"

int32_t increment(uint8_t value) {
    return value + 0;
}
```

```c filename=main.c
#include "include/types.h"

int32_t run(uint8_t value) {
    return increment(value);
}
```

```click
verifying "worker.c";
verifying "main.c";

int32 increment(uint8 value) {
    ensures result == value;
}

int32 run(uint8 value) {
    ensures result == value;
} by {
    execute();
    simp();
}
```

```expect
pass
```
