# The implicit closer drops a conjunct of `memset`'s guarded postcondition

`memset`'s library contract ends
`(0u64..bytes).all(|k| { defined(destination[k]) and destination[k] == (value as uint8) })`.
A caller that states only the values, as `bytes::all_equal` does once it is
unfolded, needs the same guarded universal without the `defined(..)`
conjunct. A guarded universal whose conclusion is a conjunction entails the
universal of any one conjunct under the same binder and guards, so the implicit closer
closes the goal from the indexed source fact with `intro()` for the binder
and its range guard, `instantiate` at the introduced variable, and
`close()`.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst) {
    memset(dst, 7, 4);
}
```

```click
import click::bytes;
verifying "fill.c";

void fill(uint8* dst) {
    owns dst[0..4];
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
}
```

```expect
pass
```
