# Pragma-once headers are expanded once per translation unit

```c filename=include/common.h
#pragma once
typedef int32 shared_t;
```

```c filename=include/left.h
#include "common.h"
typedef shared_t left_t;
```

```c filename=include/right.h
#include "common.h"
typedef shared_t right_t;
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
