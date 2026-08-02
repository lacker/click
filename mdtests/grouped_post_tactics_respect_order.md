# Grouped post-execution tactics respect source order

`simp()` closes only claims provable at its position. A fact established by a
later `have` does not retroactively affect that earlier `simp()` tactic.

```c filename=grouped_post_order.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "grouped_post_order.c";

int32 identity(int32 x) {
    ensures exists (k: int32) { k + 1 == result + 1 };
} by {
    execute();
    simp();
    have exists (k: int32) { k + 1 == result + 1 } by {
        witness(k = result);
        simp();
    }
}
```

```expect
fail: grouped `simp` could not certify its complete claim transition
```
