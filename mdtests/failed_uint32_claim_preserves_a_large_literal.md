# A failed uint32 claim retains its written literal

The claim is false, but the refusal must report the unsigned value written
in the source instead of its signed reinterpretation.

```c filename=big.c
#include <stdint.h>
uint32_t big(void) { return 1u; }
```

```click
verifying "big.c";
uint32 big() { ensures result == 2707161783u32 by auto; }
```

```expect
fail: `ensures result == 2707161783u32` failed
```
