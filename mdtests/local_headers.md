# Local headers are shared across C translation units

Quoted includes resolve relative to the including source. Header declarations
are available to every C file that includes them, while the Click sidecar
continues to verify only the translation-unit functions.

```c filename=include/types.h
#include "detail/base.h"

struct pair {
    index_t value;
};

int32 increment(int32 value);
```

```c filename=include/detail/base.h
typedef int32 index_t;
```

```c filename=worker.c
#include "include/types.h"

int32 increment(int32 value) {
    return value + 1;
}
```

```c filename=main.c
#include "include/types.h"

int32 run() {
    return sizeof(struct pair) + increment(4);
}
```

```click
verifying "worker.c";
verifying "main.c";

int32 increment(int32 value) {
    requires value < 2147483647;
    ensures result == value + 1;
}

int32 run() {
    ensures result == 9;
} by {
    execute();
    simp();
}
```

```expect
pass
```
