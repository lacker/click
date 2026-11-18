# The built-in `<string.h>` declares the standard `strlen`

Click's `<string.h>` declares `size_t strlen(const char *s)`, and a call
binds to the standard-library contract: the caller's borrowed string
`views cstr_at(s, len)`, stated over its `const char *` parameter for the value
parameter `len`, is the instance the contract views, and the call returns its
length `len`. The length is a `size_t`, as in C, so the returned index reads
the terminator without any narrowing.

Under the user-space target plain `char` is signed, so `s` points at `int8`
bytes while `cstr_at` and the `strlen` contract read `uint8` bytes. The
resource's facts state the explicit byte view `s as (uint8 *)`, the contract
accepts the `char` pointer as its byte pointer, and `s[result]`, a signed
read, is the conversion of the terminator byte the string holds at its
length, so it is zero too.

```c filename=builtin_strlen.c
#include <string.h>

size_t last_index(const char *s) {
    size_t n = strlen(s);
    return n;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "builtin_strlen.c";

uint64 last_index(const char* s) {
    let len: uint64;
    views click::c::string::cstr_at(s, len);
    ensures result == len;
    ensures s[result] == '\0';
}
```

```expect
pass
```
