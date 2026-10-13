# Signed-character C-string requirements reach a callee

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
    requires cstr_readable(src);
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}

uint64 outer(const int8* src) {
    requires cstr_readable(src);
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}
```

`measure` verifies; `outer` is refused at the call:

```expect
pass
```
