# A refused prefix does not infer a missing extent from a held range

The proof holds `a[0..n]`, and requests the larger `a[0..n + 1]`. The claim must
fail without asserting that no range was stated or inventing an extent cause
from the failure to construct a checked source proof.

```c filename=unnarrowable_range_names_held_range.c
void walk(int32 *a, int32 *b, int32 n) {
    b[0] = 1;
}
```

```click
verifying "unnarrowable_range_names_held_range.c";

void walk(int32 *a, int32 *b, int32 n) {
    views a[0..n];
    owns b[0..n];
    requires 1 <= n;
    requires n <= 1073741823;
} by {
    have viewable(a[0..n + 1]);
    execute();
    simp();
}
```

```expect
fail: no checked source proof was constructed for `viewable(
```
