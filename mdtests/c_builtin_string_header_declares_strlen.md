# The built-in `<string.h>` declares the standard `strlen`

Click's `<string.h>` declares `size_t strlen(const char *s)`, and a call
binds to the standard-library contract: the caller's `cstr_readable`
requirement, stated over its `const char *` parameter, discharges the
contract's precondition. The length is a `size_t`, as in C, so the returned
index reads the terminator without any narrowing.

Under the user-space target plain `char` is signed, so `s` points at `int8`
bytes while the predicate and the `strlen` contract read `uint8` bytes. The
requirement is elaborated to the explicit byte view `cstr_readable((uint8*)s)`,
the contract accepts the `char` pointer as its byte pointer, and `s[result]`,
a signed read, is the conversion of the byte `strlen` promises is zero, so
it is zero too.

```c filename=builtin_strlen.c
#include <string.h>

size_t last_index(const char *s) {
    size_t n = strlen(s);
    return n;
}
```

```click
target "x86_64-linux-userspace";
verifying "builtin_strlen.c";

uint64 last_index(const char* s) {
    requires cstr_readable(s);
    ensures s[result] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
