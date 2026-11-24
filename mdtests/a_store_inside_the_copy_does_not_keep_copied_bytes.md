# A store inside the copied range does not keep the copied bytes

The refusal beside `memcpy_then_terminator_keeps_copied_bytes.md`: the
terminator is stored at `dst[n - 1]`, which the guard `k < n` does not keep
apart from the read `dst[k]`. Explicit containment and separation establish
that the store leaves the source array alone. Preservation of the destination
cells is refused at the requested separation from the store's footprint.

```c filename=copy.c
#include <string.h>
void copy_n(char *dst, const char *src, unsigned long n) { memcpy(dst, src, n); dst[n - 1] = '\0'; }
```

```click
import click::bytes;
verifying "copy.c";
void copy_n(char* dst, const char* src, uint64 n) {
    views src[0u64..n];
    owns dst[0u64..n + 1u64];
    requires 1u64 <= n;
    requires n < 32u64;
    requires separate(memory(dst[0u64..n + 1u64]), memory(src[0u64..n]));
    ensures bytes::equal(dst, 0u64, src, 0u64, n);
} by {
    unfold(bytes::equal(dst, 0u64, src, 0u64, n));
    step();
    have 0 <= to_integer(n - 1u64) by { close(); }
    have to_integer(n - 1u64) < to_integer(n + 1u64) by { close(); }
    have contains(memory(dst[0u64..n + 1u64]), memory(dst[n - 1u64])) by {
        apply(click::separation::contains_element(dst, 0u64, n + 1u64, n - 1u64));
    }
    have contains(memory(src[0u64..n]), memory(src[0u64..n])) by {
        apply(click::separation::contains_refl(memory(src[0u64..n])));
    }
    have separate(memory(dst[n - 1u64]), memory(src[0u64..n])) by {
        apply(click::separation::separate_restrict(memory(dst[0u64..n + 1u64]), memory(src[0u64..n]), memory(dst[n - 1u64]), memory(src[0u64..n])));
    }
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, n) by {
        have forall (k: uint64) { k < n implies
            (dst as (uint8 *))[k] == at(copied, (dst as (uint8 *))[k])
        } by {
            intro(); intro();
            have separate(statement(1).footprint, memory((dst as (uint8 *))[k])) by { close(); }
            preserve(memory((dst as (uint8 *))[k]), statement(1));
        }
        close();
    }
}
```

```expect
fail: goal: separate(region(1).footprint, dst[…])
```
