# Signed indices preserve their offset semantics

```click
import click::separation;
theorem signed_bytes(p: uint8*, i: int32, j: int32) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j])) by {
        apply(separation::separate_elements(p, i, j));
        close();
    }
}
theorem signed_words(p: int32*, i: int64, j: int64) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j])) by {
        apply(separation::separate_elements(p, i, j));
        close();
    }
}
theorem negative_byte(p: uint8*) {
    ensures separate(memory(p[-1]), memory(p[0])) by {
        apply(separation::separate_elements(p, -1, 0));
        close();
    }
}
theorem unsigned_zero(p: uint8*, i: uint64) {
    requires i != 0;
    ensures separate(memory(p[i]), memory(p[0])) by {
        have separate(memory(p[0]), memory(p[i])) by {
            apply(separation::separate_elements(p, 0u64, i));
            close();
        }
        apply(separation::separate_elements(p, i, 0u64));
        close();
    }
}
```

```expect
pass
```
