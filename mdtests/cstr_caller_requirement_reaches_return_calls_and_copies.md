# A caller's C-string requirement reaches `strlen` in a `return` and through a copy

Equivalent C forms verify alike. A caller that views a string
`cstr_at(s, n)` lends it to `strlen` when the call is the returned
expression, and when the pointer reaches the call through a local copy with
no store in between.

```c filename=cstr_return_and_copy.c
#include <string.h>

size_t returned(const char *s) {
    return strlen(s);
}

uint64 copied(uint8 bytes[]) {
    uint8* p;
    p = bytes;
    return strlen(p);
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "cstr_return_and_copy.c";

uint64 returned(const char* s) {
    let n: uint64;
    views click::c::string::cstr_at(s, n);
    ensures result == n;
    ensures s[result] == '\0';
}

uint64 copied(uint8 bytes[]) {
    let n: uint64;
    views click::c::string::cstr_at(bytes, n);
    ensures result == n;
    ensures bytes[result] == '\0';
}
```

```expect
pass
```
