# memcpy accepts a const unsigned char source

```c filename=memcpy_const_unsigned_char_source.c
#include <string.h>
void copy4(char *dst, const unsigned char *src) { memcpy(dst, src, 4); }
```

```click
verifying "memcpy_const_unsigned_char_source.c";
void copy4(char* dst, const uint8* src) {
    requires viewable(src[0..4]);
    owns dst[0..4];
    requires separate(memory(dst[0..4]), memory(src[0..4]));
} by { execute(); simp(); }
```

```expect
pass
```
