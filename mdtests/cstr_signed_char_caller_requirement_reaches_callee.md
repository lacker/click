# Signed-character C-string requirements reach a callee

`outer` lends its borrowed signed-character string `cstr_at(src, len)` to
`measure`, which lends it to `strlen` through a `const char *` cast.

```c filename=measure.c
#include <string.h>

unsigned long measure(const signed char *src)
{
	return strlen((const char*)src);
}

unsigned long outer(const signed char *src)
{
	unsigned long n = measure(src);
	return n;
}
```

```click
verifying "measure.c";

uint64 measure(const int8* src) {
    let len: uint64;
    views click::c::string::cstr_at(src, len);
    ensures result == len;
    ensures src[result] == '\0';
}

uint64 outer(const int8* src) {
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
