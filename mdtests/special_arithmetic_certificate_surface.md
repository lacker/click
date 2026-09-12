# Explicit special arithmetic certificates

Pointer alignment can be checked directly by the typed special certificate
family. The explicit form is retained during expansion and does not rerun
smart planning.

```c filename=special_arithmetic_certificate_surface.c
int32 special_arithmetic_certificate_surface(uint8* p) {
    return 0;
}
```

```click
verifying "special_arithmetic_certificate_surface.c";

int32 special_arithmetic_certificate_surface(uint8* p) {
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
