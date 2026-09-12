# a ranked loop may call a contract-less inline helper

An inline body executes at the call site with no contract boundary, so
termination reads the helper as a node of `drain`'s own call graph. Both
helpers here are straight-line over terminating callees, so they terminate by
construction and `decreases n;` is the whole of the obligation. `predecessor`
calls `shrink`, so the helper reached only through another helper is read too.

```c filename=include/step.h
#ifndef STEP_H
#define STEP_H
static inline int32 shrink(int32 value) {
    return value - 1;
}

static inline int32 predecessor(int32 value) {
    return shrink(value);
}
#endif
```

```c filename=c_decreases_loop_inline_helper.c
#include "include/step.h"

int32 drain(int32 n) {
    while (n > 0) {
        n = predecessor(n);
    }
    return n;
}
```

```click
verifying "c_decreases_loop_inline_helper.c";

int32 drain(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by simp;
        preserve by {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
            }
            step();
            close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and {
                    both { arithmetic() using { 0 <= n; } }
                    and { arithmetic() using { 0 <= n; } }
                }
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
