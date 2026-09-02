# a bare conjunct beside a guarded one is not a finite universal

`(0 <= k and k < 3) implies 0 <= k` is vacuous outside `0..3`, but the bare
conjunct `k < 3` is false at `k = 5`. The guard bounds only its own
implication, so the universal may not be proved by instantiating `0..3`.

```c filename=c_finite_forall_rejects_bare_conjunct.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "c_finite_forall_rejects_bare_conjunct.c";

int32 identity(int32 x) {
    ensures bad: forall (k: int32) { ((0 <= k and k < 3) implies 0 <= k) and (k < 3) };
} by {
    execute();
    simp();
}
```

```expect
fail: identity.bad
```
