# an inline helper's ranked loop is planned where its body runs

A sidecar contract names a `static inline` helper with its ordinary spelling,
but the body executes under a translation-unit-qualified name, and that is the
name its call sites carry. A termination plan is keyed by the executing name,
so the helper's own `decreases value;` reaches the function the call graph
mentions instead of a spelling nothing calls.

The call passes a constant, so the helper's loop unrolls concretely at the
call site; the ranking proof it carries is what certifies its termination.

```c filename=include/drain.h
#ifndef DRAIN_H
#define DRAIN_H
static inline int32 drain_to_zero(int32 value) {
    while (value > 0) {
        value = value - 1;
    }
    return value;
}
#endif
```

```c filename=inline_helper_ranked_loop.c
#include "include/drain.h"

int32 run(int32 n) {
    return drain_to_zero(3);
}
```

```click
verifying "inline_helper_ranked_loop.c";

int32 drain_to_zero(int32 value) {
    requires value >= 0;
    ensures result == 0;
} by {
    loop {
        decreases value;
        invariant value >= 0;
        initialize by simp;
        preserve by {
            have 0 <= value - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(value)) using { value > 0; }
            }
            step();
            close_invariants by {
                both { arithmetic() using { 0 <= value; } }
                and {
                    both { arithmetic() using { 0 <= value; } }
                    and { arithmetic() using { 0 <= value; } }
                }
            }
        }
    }
    step();
    simp();
}

int32 run(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
