# A byte read through a `char *` prints its byte view

`bytes::equal` reads `uint8` bytes, so unfolding it for `char *` arguments
gives facts about `uint8` reads through `char` pointers. A bare
`*&dst[k]` would read a `char`, so a premise prints the read through an
explicit byte view, `*(&dst[k] as (uint8 *))`, which a proof can
copy and which lowers back to the same read. Restating the fact with the
`char` reads `*&dst[0u64 + k]` is refused, and the refusal lists the byte
view premise.

```c filename=c.c
#include <string.h>
void copy_c(char *dst, const char *src) { memcpy(dst, src, 4); }
```

```click
import click::bytes;
verifying "c.c";
void copy_c(char* dst, const char* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        step();
        step();
        unfold(bytes::equal(dst, 0u64, old(src), 0u64, 4u64));
        have forall (k: uint64) { true and k < 4u64 implies *(&dst[0u64 + k] as (uint8 *)) == old(*(&src[0u64 + k] as (uint8 *))) } by {
            close();
        }
        have forall (k: uint64) { true and k < 4u64 implies *&dst[0u64 + k] == old(*&src[0u64 + k]) } by {
            close();
        }
        close();
    }
}
```

```expect
fail: forall (k: uint64) { true and k < 4u64 implies at(<state A>, *(&dst[k] as (uint8 *))) == old(*(&src[k] as (uint8 *))) }
```
