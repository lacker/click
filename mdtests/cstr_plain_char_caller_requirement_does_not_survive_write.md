# Plain char cstr forwarding

`outer` owns the string `cstr_at(src, len)` and unfolds it to write its first
byte. After the write it holds the bytes, not a string, so the call to
`measure`, which views `cstr_at(src, len)` for its own `len`, has no instance to take the length
from.

```c filename=measure.c
#include <string.h>

unsigned long measure(const char *src)
{
	return strlen(src);
}

unsigned long outer(char *src)
{
	src[0] = 'x';
	unsigned long n = measure(src);
	return n;
}
```

```click
verifying "measure.c";

uint64 measure(const char* src) {
    let len: uint64;
    views click::c::string::cstr_at(src, len);
    ensures result == len;
    ensures src[result] == '\0';
}

uint64 outer(char* src) {
    let len: uint64;
    owns click::c::string::cstr_at(src, len);
    ensures src[result] == '\0';
} by {
    unfold(click::c::string::cstr_at(src, len));
}
```

`measure` verifies; `outer` is refused at the call:

```expect
fail: call to `measure` needs a held `cstr_at` instance to give `len` its value
```
