# Const-source copy preserves ownership for the terminator

```c filename=memcpy_const_source_terminator.c
#include <string.h>
void copy_prefix(char *dst, const char *src, unsigned long n) {
    memcpy(dst, src, n);
    dst[n] = '\0';
}
```

```click
verifying "memcpy_const_source_terminator.c";
void copy_prefix(char* dst, const char* src, uint64 n) {
    requires n < 32u64;
    requires viewable(src[0u64..n]);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..n]));
    ensures dst[n] == '\0';
} by { execute(); simp(); }
```

```expect
pass
```
