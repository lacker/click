# A failed uint32 claim retains the unsigned high bit

The smallest uint32 literal that cannot be represented as a positive int32
must stay unsigned in the refused claim's label.

```c filename=big.c
#include <stdint.h>
uint32_t big(void) { return 1u; }
```

```click
verifying "big.c";
uint32 big() { ensures result == 2147483648u32 by auto; }
```

```expect
fail: `ensures result == 2147483648u32` failed
```
