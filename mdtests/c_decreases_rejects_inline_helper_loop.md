# an inline helper's own loop still needs its own ranking

An inline body executes at its call site, so termination reads it as a
call-graph node rather than as an opaque callee. That treatment cuts both
ways: `halve_down` contains a loop, and a loop needs a checked ranking
wherever it runs, so `drain`'s own `decreases n;` is not enough.

The call here passes a constant, so the helper's loop unrolls concretely and
the contract of `drain` is proved; only its termination claim is refused.

```c filename=include/halve.h
#ifndef HALVE_H
#define HALVE_H
static inline int32 halve_down(int32 value) {
    while (value > 1) {
        value = value - 2;
    }
    return value;
}
#endif
```

```c filename=c_decreases_rejects_inline_helper_loop.c
#include "include/halve.h"

int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return halve_down(4);
}
```

```click
verifying "c_decreases_rejects_inline_helper_loop.c";

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
    execute();
    simp();
}
```

```expect
fail: could not certify termination for `drain`: every reachable loop, recursive cycle, and callee must have a checked ranking proof
```
