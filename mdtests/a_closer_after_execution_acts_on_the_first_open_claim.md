# A closer after execution acts on the first open claim

After execution the open goals are the proposition claims, in contract order,
and a closer acts on the first of them. Here the first claim is `n == 0`,
which no available fact states, so `close()` is refused for that goal. It
does not look further down the list for a claim it could close, as it used to:
`result == n` waits for its turn.

```c filename=a_closer_after_execution_acts_on_the_first_open_claim.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "a_closer_after_execution_acts_on_the_first_open_claim.c";

int32 f(int32 n) {
    ensures n == 0;
    ensures result == n;
} by {
    step_until(function.exit);
    close();
    normalize();
}
```

```expect
fail: `ensures n == 0` failed for `f.ensures_0` path 0
```
