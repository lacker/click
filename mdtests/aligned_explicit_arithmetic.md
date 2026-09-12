# Alignment closes by an explicit special arithmetic certificate

The explicit typed certificate names the base fact and checks the alignment
directly, with no search.

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
        arithmetic_certificate special {
            premise 0: aligned(p, 16) => aligned(p, 16);
            pointer_alignment premise 0 => aligned(p + 24, 8);
            conclusion 0;
        }
    }
    simp();
}
```

```expect
pass
```
