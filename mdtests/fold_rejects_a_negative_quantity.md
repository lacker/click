# fold rejects a negative quantity

`fold(n of R(a))` requires `n` to be proved zero or positive, and it reads
`n` twice: once for that gate, and once to decide whether the population's
body is active and so consumed.

A resource quantity is a signed `int32`, and the constant arm asked
`quantity.as_const()`, which answers `u32`. `-1` arrived as `4294967295`,
which is positive by that reading, so the gate passed and the body went
active. The symbolic arm beside it always asked
`Bitvector32SignedGreaterThan`, so the two arms disagreed about the same
number.

    fold(-1 of ref(o));

verified, and the population it left really does count `-1`: stating
`ensures count(ref(o)) == 0` afterwards reports "left side evaluated to -1".
Nothing in the corpus spends that, because `resource_quantity_at_least` is
signed and `owns -1 of R` entails no positive count — but the step is
accepted and the ghost state is one a nonnegative count invariant cannot
describe.

Reading the constant signed is what makes the two arms agree.
`folds_a_zero_quantity` beside it is the boundary the gate does admit, where
the body stays inactive.

```c filename=fold_rejects_a_negative_quantity.c
struct s { int32 x; };

int32 mint(struct s* o) {
    return 0;
}

int32 mint_zero(struct s* o) {
    return 0;
}
```

```click
resource ref(o: struct s*) {
    owns o->x;
}

verifying "fold_rejects_a_negative_quantity.c";

int32 mint_zero(struct s* o) {
    requires o != 0;
    requires count(ref(o)) == 0;
    owns o->x;
    ensures result == 0;
} by {
    execute();
    fold(0 of ref(o));
    simp();
}

int32 mint(struct s* o) {
    requires o != 0;
    requires count(ref(o)) == 0;
    owns o->x;
    ensures result == 0;
} by {
    execute();
    fold(-1 of ref(o));
    simp();
}
```

```expect
fail: `fold(-1 of ref(o))` requires its quantity to be proved zero or positive
```
