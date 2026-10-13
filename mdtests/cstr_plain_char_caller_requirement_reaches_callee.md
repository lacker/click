# Plain char cstr forwarding

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
    requires cstr_readable(src);
    ensures src[result] == '\0';
} by {
    execute();
    simp();
}

uint64 outer(const char* src) {
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
