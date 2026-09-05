# Alignment closes by the simple `arithmetic using` step

The smart `simp` closure of an alignment goal expands to one explicit
`arithmetic() using` step naming the base fact. Writing that step by hand
checks the same rule directly, with no search.

```c filename=aligned_explicit_arithmetic.c
int32 aligned_explicit_arithmetic(uint8* p) {
    return 0;
}
```

```click
verifying "aligned_explicit_arithmetic.c";

int32 aligned_explicit_arithmetic(uint8* p) {
    requires aligned(p, 16);
    ensures aligned(p + 24, 8);
} by {
    execute();
    have aligned(p + 24, 8) by {
        arithmetic() using {
            aligned(p, 16);
        }
    }
    simp();
}
```

```expect
pass
```
