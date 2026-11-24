# solve splits off a new fold element whose contribution is zero

After `v[i] = 1`, the added element contributes zero to the zero count.
Unfolding and the fold append law reduce the claim to preservation of the
unchanged `0..i` prefix. Framing itself still uses identical endpoints.

```c filename=fold_read_solve_extends_endpoint_with_zero_contribution.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_solve_extends_endpoint_with_zero_contribution.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i + 1) == old(zeros(v, 0, i));
} by {
    mark entry;
    have zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i) by close();
    step();
    have zeros(at(entry, v), 0, i) == zeros(v, 0, i + 1) by {
        close();
        close();
    }
}
```

```expect
pass
```
