# Predicate array arguments name their states

The call postcondition reads `src` before the copy. A later state of
the same pointer must remain visibly distinct in the missing-fact report.

```c filename=t.c
#include <string.h>
void copy_t(char *dst, const char *src) { memcpy(dst, src, 4); dst[4] = '\0'; }
```

```click
import click::bytes;
verifying "t.c";
void copy_t(char* dst, const char* src) {
    views src[0..4];
    owns dst[0..5];
    requires separate(memory(dst[0..5]), memory(src[0..4]));
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by {
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        transport(at(copied, bytes::equal(dst, 0u64, src, 0u64, 4u64)), bytes::equal(dst, 0u64, src, 0u64, 4u64));
    }
}
```

```expect
fail: missing pure fact: click::bytes::equal(at(<state A>, dst), 0u64, at(<state A>, src), 0u64, 4u64)
```
