# a recursive inline helper is a cycle, not a straight line

`step_down` calls itself, so its inlined body is a recursive cycle in the
caller's call graph. A cycle needs a checked ranking rule of its own, and a
contract-less helper has none, so `drain`'s `decreases n;` is refused.

The call passes a constant, so the recursion unrolls concretely and the
contract of `drain` is proved; only its termination claim is refused.

```c filename=include/step_down.h
#ifndef STEP_DOWN_H
#define STEP_DOWN_H
static inline int32 step_down(int32 value) {
    if (value > 0) {
        return step_down(value - 1);
    }
    return 0;
}
#endif
```

```c filename=c_decreases_rejects_recursive_inline_helper.c
#include "include/step_down.h"

int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return step_down(2);
}
```

```click
verifying "c_decreases_rejects_recursive_inline_helper.c";

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
