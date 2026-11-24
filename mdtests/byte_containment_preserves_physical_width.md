# Byte containment uses physical spans

A byte at offset seven is contained in an eight-byte cell, even though its
address is not aligned to the parent's element width.

```click quick-solve
theorem last_byte(p: uint64*) {
    ensures contains(memory(p[0..1]), memory((p as (uint8 *))[7..8])) by {
        close();
    }
}
```

```expect
pass
```
