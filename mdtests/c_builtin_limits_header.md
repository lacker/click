# Built-in `<limits.h>`

Click's `<limits.h>` defines the integer limits of the LP64 layout every
target selects. `CHAR_MIN` and `CHAR_MAX` follow the target's plain `char`:
the kernel target's is unsigned, so `CHAR_MIN` is 0 here
(`userspace_char_limits_are_signed.md` covers the signed user-space values).
The header is available on every target, and its macros work in
preprocessor conditions as well as in code.

```c filename=builtin_limits.c
#include <limits.h>

#if INT_MAX != 2147483647 || CHAR_MIN != 0
#error unexpected limits
#endif

int limits_sum(void) {
    int bits = CHAR_BIT;
    int top = INT_MAX - 2147483600;
    unsigned int all = UINT_MAX;
    unsigned char byte = UCHAR_MAX;
    if (all != 4294967295U) {
        return 0;
    }
    return bits + top + (byte - 250) + (INT_MIN + 2147483647 + 1);
}
```

```click
target "x86_64-linux-kernel";
verifying "builtin_limits.c";

int limits_sum() {
    ensures result == 60;
} by {
    execute();
    simp();
}
```

```expect
pass
```
