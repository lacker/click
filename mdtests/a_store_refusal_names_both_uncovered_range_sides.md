# a store refusal names both uncovered range sides

The held `owns b[i..n]` may start after `b[0]`, and `n` may be too small for
it to reach `b[1]`. The refusal used to print only the missing `owns b[0..1]`,
since the note that explains an endpoint comparison appeared only when the
held and needed ranges shared a start. It now names each side the verdict
could not establish.

```c filename=a_store_refusal_names_both_uncovered_range_sides.c
void walk(int32 *b, int32 i, int32 n) {
    b[0] = 1;
}
```

```click
verifying "a_store_refusal_names_both_uncovered_range_sides.c";

void walk(int32 *b, int32 i, int32 n) {
    owns b[i..n];
    requires 0 <= i and i < n;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns b[0..1]`
  note: held `owns b[i..n]` covers `b[0..1]` only when `i <= 0` and `1 <= n`
```
