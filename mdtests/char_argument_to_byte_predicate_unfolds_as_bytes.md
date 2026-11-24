# A `char *` argument to a byte predicate unfolds to the same byte reads

`bytes::equal` reads `uint8` bytes. A `char *` argument is passed as its
explicit byte view, so the call's `memcpy` postcondition and the caller's
written postcondition are one instance. Unfolding the caller's goal reads the
same `uint8` loads the call's fact does, not `(int8)` conversions of them, so
`copy_c` verifies exactly as `copy_u` does.

```c filename=c.c
#include <string.h>
void copy_u(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); }
void copy_c(char *dst, const char *src) { memcpy(dst, src, 4); }
```

```click
import click::bytes;
verifying "c.c";
void copy_u(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        step();
        have separate(statement(0).footprint, memory(src[0..4])) by {
            close() using { separate(memory(dst[0..4]), memory(src[0..4])); };
        }
        have contains(statement(0).footprint, statement(0).footprint) by {
            apply(click::separation::contains_refl(statement(0).footprint));
        }
        have contains(memory(src[0..4]), memory(src[0u64..4u64])) by { normalize(); }
        have forall (k: uint64) { k < 4u64 implies src[k] == old(src[k]) } by {
            intro();
            intro();
            have contains(memory(src[0u64..4u64]), memory(src[k])) by {
                apply(click::separation::contains_element(src, 0u64, 4u64, k));
            }
            have contains(memory(src[0..4]), memory(src[k])) by {
                apply(click::separation::contains_trans(memory(src[0..4]), memory(src[0u64..4u64]), memory(src[k])));
            }
            have separate(statement(0).footprint, memory(src[k])) by {
                apply(click::separation::separate_restrict(statement(0).footprint, memory(src[0..4]), statement(0).footprint, memory(src[k])));
            }
            have src[k] == at(statement(0).entry, src[k]) by {
                preserve(memory(src[k]), statement(0));
            }
            close();
        }
        step();
        unfold(bytes::equal(dst, 0u64, old(src), 0u64, 4u64));
        have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
            unfold(bytes::equal(dst, 0u64, src, 0u64, 4u64));
            intro();
            intro();
            instantiate(forall (k1: uint64) { true and k1 < 4u64 implies dst[0u64 + k1] == old(src[0u64 + k1]) }, k);
            instantiate(forall (k1: uint64) { k1 < 4u64 implies src[k1] == old(src[k1]) }, k);
            rewrite(src[k], old(src[k]));
            close();
        }
        close();
    }
}
void copy_c(char* dst, const char* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        step();
        have separate(statement(0).footprint, memory(src[0..4])) by {
            close() using { separate(memory(dst[0..4]), memory(src[0..4])); };
        }
        have contains(statement(0).footprint, statement(0).footprint) by {
            apply(click::separation::contains_refl(statement(0).footprint));
        }
        have contains(memory(src[0..4]), memory(src[0u64..4u64])) by { normalize(); }
        have forall (k: uint64) { k < 4u64 implies *(&src[k] as (uint8 *)) == old(*(&src[k] as (uint8 *))) } by {
            intro();
            intro();
            have contains(memory(src[0u64..4u64]), memory(src[k])) by {
                apply(click::separation::contains_element(src, 0u64, 4u64, k));
            }
            have contains(memory(src[0..4]), memory(src[k])) by {
                apply(click::separation::contains_trans(memory(src[0..4]), memory(src[0u64..4u64]), memory(src[k])));
            }
            have separate(statement(0).footprint, memory(src[k])) by {
                apply(click::separation::separate_restrict(statement(0).footprint, memory(src[0..4]), statement(0).footprint, memory(src[k])));
            }
            have *(&src[k] as (uint8 *)) == at(statement(0).entry, *(&src[k] as (uint8 *))) by {
                preserve(memory(src[k]), statement(0));
            }
            close();
        }
        step();
        unfold(bytes::equal(dst, 0u64, old(src), 0u64, 4u64));
        have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
            unfold(bytes::equal(dst, 0u64, src, 0u64, 4u64));
            intro();
            intro();
            instantiate(forall (k1: uint64) { true and k1 < 4u64 implies *(&dst[0u64 + k1] as (uint8 *)) == old(*(&src[0u64 + k1] as (uint8 *))) }, k);
            instantiate(forall (k: uint64) { k < 4u64 implies *(&src[k] as (uint8 *)) == old(*(&src[k] as (uint8 *))) }, k);
            rewrite(*(&src[k] as (uint8 *)), old(*(&src[k] as (uint8 *))));
                close();
        }
        close();
    }
}
```

```expect
pass
```
