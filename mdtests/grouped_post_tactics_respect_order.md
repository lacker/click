# Grouped post-execution tactics respect source order

`close()` closes only claims provable at its position. A fact established by a
later `have` does not retroactively affect that earlier `close()` tactic.

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
    step_until(function.exit);
    close();
    have exists (k: int32) { k + 1 == result + 1 } by {
        witness(result);
        close();
    }
}
```

```expect
fail: unclosed goal: exists
```
