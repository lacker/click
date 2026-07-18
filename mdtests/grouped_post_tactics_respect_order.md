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
    ensures exists (int32 k) { k == result };
} by {
    execute_rest();
    simp();
    have exists (int32 k) { k == result } by {
        witness(k = result);
        simp();
    }
}
```

```expect
fail: left `identity.ensures_0` unproved
```
