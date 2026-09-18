# `arithmetic()` sharpens a bound with a disequality

`n >= 0` and `n != 0` say `0 < n`. The certificate had no step that combined
a bound with a disequality, so the strict bound was out of reach even though
both facts were cited. `lt_from_neq` is that step: a non-strict bound and a
disequality on the same two sides (in either spelling) give the strict bound,
because integers have nothing between `0` and `1`.

```c filename=arithmetic_sharpens_a_bound_with_a_disequality.c
int32 sharpen(int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_sharpens_a_bound_with_a_disequality.c";

int32 sharpen(int32 n) {
    requires n >= 0;
    requires n != 0;
    ensures result == 0;
} by {
    have 0 < n by { arithmetic() using { n >= 0; n != 0; } }
    step();
    simp();
}
```

```expect
pass
```
