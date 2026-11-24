# Guarded definedness survives a disjoint store

The terminator store leaves the initialized prefix and its values unchanged.
Value and definedness preservation use explicit separation and ordinary
`preserve` steps.

```c filename=fill.c
#include <string.h>
void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

```click
import click::bytes;
import click::separation;
verifying "fill.c";
void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by {
    step(); step(); step();
    have (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }) by {
        intro(); intro();
        have separate(memory(dst[4u64]), memory(dst[k])) by {
            apply(separation::separate_elements(dst, 4u64, k));
        }
        have separate(statement(1).footprint, memory(dst[k])) by {
            close() using { separate(memory(dst[4u64]), memory(dst[k])); };
        }
        have at(statement(1).exit, dst[k]) == at(statement(1).entry, dst[k]) by {
            preserve(memory(dst[k]), statement(1));
        }
        instantiate(at(statement(1).entry,
            (0u64..4u64).all(|j| { defined(dst[j]) and dst[j] == 7 })), k);
        have at(statement(1).exit, defined(dst[k])) by {
            preserve(memory(dst[k]), statement(1));
        }
        have defined(dst[k]) by { close(); }
        have dst[k] == 7u8 by { close(); }
        close();
    }
    have bytes::all_equal(dst, 0u64, 4u64, 7u8) by {
        unfold(bytes::all_equal(dst, 0u64, 4u64, 7u8));
        intro(); intro();
        instantiate((0u64..4u64).all(|j| { defined(dst[j]) and dst[j] == 7 }), k);
        close();
    }
    close();
}
```

```expect
pass
```
