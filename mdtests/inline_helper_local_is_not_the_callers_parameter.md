# An inline helper's local is not the caller's parameter of that name

A parameter the caller never addresses is held as a value, not as storage, but
it is still that caller's object. An inlined helper declaring a local of the
same name must not become it: `p` still reads what the caller was passed.

```c filename=include/hsetp.h
#ifndef HSETP_H
#define HSETP_H
static inline int32 setp(int32 seed) {
    int32 p;
    p = seed;
    return 0;
}
#endif
```

```c filename=t.c
#include "include/hsetp.h"

int32 param_clash(int32 p) {
    int32 ignored;
    ignored = setp(7);
    return p;
}
```

```click
verifying "t.c";

int32 param_clash(int32 p) {
    requires p == 1;
    ensures result == 7;
}
```

```expect
fail: left side evaluated to p
```
