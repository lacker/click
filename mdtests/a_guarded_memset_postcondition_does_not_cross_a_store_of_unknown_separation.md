# A guarded `memset` postcondition does not cross a store of unknown separation

After `memset(dst, 7, 4)` the function stores through `slot`, a pointer the
contract places only somewhere in `dst[0..5]`. It may be one of the first
four cells, so the claim that they are all `7` must be refused: neither the
`defined(..)` read nor the value read is shown separate from the store.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst, unsigned long i) {
    unsigned char *slot = dst + i;
    memset(dst, 7, 4);
    *slot = 0;
}
```

```click
verifying "fill.c";

void fill(uint8* dst, uint64 i) {
    owns dst[0..5];
    requires i < 5u64;
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    step();
    step();
    step();
    mark filled;
    step();
    have (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }) by { close(); }
}
```

```expect
fail: `solve` failed
```
