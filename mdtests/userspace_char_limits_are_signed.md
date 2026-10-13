# User-space `CHAR_MIN` and `CHAR_MAX` are the signed byte range

The user-space target follows the x86-64 System V ABI, whose plain `char`
is signed, so `<limits.h>` gives `CHAR_MIN` and `CHAR_MAX` the values of
`SCHAR_MIN` and `SCHAR_MAX`, and the target does not predefine
`__CHAR_UNSIGNED__`. The kernel target keeps unsigned plain `char`
(`c_builtin_limits_header.md`).

```c filename=userspace_char_limits.c
#include <limits.h>

#if CHAR_MAX != 127
#error plain char is not signed
#endif

#ifdef __CHAR_UNSIGNED__
#error user space predefines __CHAR_UNSIGNED__
#endif

int char_range(void) {
    if (CHAR_MIN != SCHAR_MIN) {
        return 0;
    }
    return CHAR_MAX - CHAR_MIN;
}
```

```click
target "x86_64-linux-userspace";
verifying "userspace_char_limits.c";

int32 char_range() {
    ensures result == 255;
} by {
    execute();
    simp();
}
```

```expect
pass
```
