# Smart arithmetic names an `int32` atom, not its `uint32` cast

`arithmetic()` bounds `m` below `2147483647` from `m < n` through `n`'s own
`int32` range, a certificate node `int32_range => n <= 2147483647`. The
surface certificate spells each atom with a source expression that lowers to
the same term, and `((uint32)n)` in the other listed premise lowers to the
same raw bits as `n`. It is not the same typed value: `((uint32)n) <=
2147483647` is an unsigned comparison, so a certificate that spelled the atom
that way did not re-lower to the node the kernel checked, and the smart tactic
failed with "addition result does not encode the child sum". An atom is now
spelled only by an expression that reads it as an `int32`.

`bounded_by_expansion` is what `click expand` prints for `bounded`, checked as
written.

```c filename=arithmetic_names_an_int32_atom_beside_its_uint32_cast.c
int32 bounded(int32 m, int32 n) {
    return m;
}

int32 bounded_by_expansion(int32 m, int32 n) {
    return m;
}
```

```click
verifying "arithmetic_names_an_int32_atom_beside_its_uint32_cast.c";

int32 bounded(int32 m, int32 n) {
    requires m < n;
    requires ((uint32)n) <= 1073741823u32;
    ensures result < 2147483647;
} by {
    have m < 2147483647 by {
        arithmetic() using { m < n; ((uint32)n) <= 1073741823u32; }
    }
    execute();
    simp();
}

int32 bounded_by_expansion(int32 m, int32 n) {
    requires m < n;
    requires ((uint32)n) <= 1073741823u32;
    ensures result < 2147483647;
} by {
    have m < 2147483647 by {
        arithmetic_certificate signed_int32 {
            premise 0: m < n => m < n;
            int32_range => n <= 2147483647;
            add 0, 1 => (m + n) < (n + 2147483647);
            interval_from_affine 2 (m) (-2147483648) (2147483646);
            interval_atom (2147483647) (2147483647) (2147483647);
            interval_compare 3, 4 lt => m < 2147483647;
            conclusion 5;
        }
    }
    step();
    have result < 2147483647 by {
        assumption();
    }
    assumption();
}
```

```expect
pass
```
