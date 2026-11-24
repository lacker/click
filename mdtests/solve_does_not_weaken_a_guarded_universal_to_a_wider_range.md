# `solve` does not drop a conjunct under a different guard

Dropping a conjunct of a guarded universal keeps its binder and guards
exactly. `memset(dst, 7, 4)` states its values only for `k < 4`; the claim
for `k < 5` has a different guard, so the four-byte postcondition does not
supply it, and the fifth byte is in fact unknown.

```c filename=fill_short.c
#include <string.h>

void fill_short(unsigned char *dst) {
    memset(dst, 7, 4);
}
```

```click
verifying "fill_short.c";

void fill_short(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..5u64).all(|k| { dst[k] == 7u8 });
} by {
    step_until(function.exit);
    close();
    close();
}
```

```expect
fail: `close` search did not retain a complete proof
```
