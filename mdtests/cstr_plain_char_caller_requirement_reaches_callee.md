# Plain char cstr forwarding

`outer` lends the string it views, `cstr_at(src, len)`, to `measure`, which
lends it to `strlen`; each contract's value parameter `len` is the same length.

```c filename=measure.c
#include <string.h>

unsigned long measure(const char *src)
{
	return strlen(src);
}

unsigned long outer(const char *src)
{
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

uint64 outer(const char* src) {
    let len: uint64;
    views click::c::string::cstr_at(src, len);
    ensures result == len;
    ensures src[result] == '\0';
}
```

`measure` and `outer` verify:

```expect
pass
```
