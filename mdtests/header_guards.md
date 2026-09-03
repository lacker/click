# Guarded headers are expanded once per translation unit

Repeated inclusion through different header paths must not duplicate a
guarded declaration.

```c filename=include/common.h
#ifndef COMMON_H
#define COMMON_H
typedef int32 shared_t;
#endif // COMMON_H
```

```c filename=include/left.h
#ifndef LEFT_H
#define LEFT_H
#include "common.h"
typedef shared_t left_t;
#endif
```

```c filename=include/right.h
#ifndef RIGHT_H
#define RIGHT_H
#include "common.h"
typedef shared_t right_t;
#endif
```

```c filename=main.c
#include "include/left.h"
#include "include/right.h"

int32 run() {
    return sizeof(left_t) + sizeof(right_t);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 8;
} by {
    execute();
    simp();
}
```

```expect
pass
```
