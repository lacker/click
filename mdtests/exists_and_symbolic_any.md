# exists and symbolic range any can be reused as facts

This checks the first existential proposition slice. Click can parse explicit
`exists`, lower symbolic `(lo..hi).any(...)` to a kernel existential, and reuse
matching assumptions. Existential goal introduction is covered separately by the
explicit `witness` proof step.

```c filename=exists_and_symbolic_any.c
int32 exists_and_symbolic_any(int32 x, int32 n) {
    return x;
}
```

```click
verifying "exists_and_symbolic_any.c";

int32 exists_and_symbolic_any(int32 x, int32 n) {
    requires exists (int32 k) { k == x };
    requires (0..n).any(|k| { k == x });
    ensures same_exists: exists (int32 k) { k == x } by auto;
    ensures same_any: (0..n).any(|k| { k == x }) by auto;
    ensures concrete_any_still_unrolls: (0..3).any(|k| { k == 1 }) by auto;
}
```

```expect
pass
```
