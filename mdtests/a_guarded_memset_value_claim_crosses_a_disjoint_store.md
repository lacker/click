# A `memset` value claim crosses a disjoint store

`bytes::all_equal` unfolds to the values in the filled prefix. For each
index, the proof states cell separation, preserves the read across the store,
and instantiates `memset`'s historical postcondition. It does not rely on an
extra ownership composition inferred at the call.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst) {
    memset(dst, 7, 4);
    dst[4] = 0;
}
```

```click
import click::bytes;
import click::separation;
verifying "fill.c";

void fill(uint8* dst) {
    owns dst[0..5];
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by {
    step();
    step();
    have bytes::all_equal(dst, 0u64, 4u64, 7u8) by {
        unfold(bytes::all_equal(dst, 0u64, 4u64, 7u8));
        intro(); intro();
        have separate(memory(dst[4u64]), memory(dst[k])) by {
            apply(separation::separate_elements(dst, 4u64, k));
        }
        have separate(statement(1).footprint, memory(dst[k])) by {
            close() using { separate(memory(dst[4u64]), memory(dst[k])); };
        }
        have dst[k] == at(statement(1).entry, dst[k]) by {
            preserve(memory(dst[k]), statement(1));
        }
        instantiate(at(statement(1).entry,
            (0u64..4u64).all(|j| { defined(dst[j]) and dst[j] == 7 })), k);
        close();
    }
    step();
    close();
}
```

```expect
pass
```
