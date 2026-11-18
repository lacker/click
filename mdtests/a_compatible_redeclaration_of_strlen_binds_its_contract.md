# A compatible redeclaration of `strlen` binds its contract

A program may declare a library function itself instead of including its
header (C11 7.1.4p2), provided the declaration is compatible with the
library's. This one spells `size_t` as `unsigned long`, the type it names on
every Click target, and qualifies the parameter itself with `const`, which a
function's type ignores (C11 6.7.6.3p15). GCC 14 and Clang accept it without
a diagnostic, and the call binds to the standard-library contract for
`strlen`, as it does through `<string.h>`: it views the caller's string and
returns its length.

```c filename=main.c
unsigned long strlen(const char *const s);
unsigned long last_index(const char *s) {
    unsigned long n = strlen(s);
    return n;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "main.c";

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
