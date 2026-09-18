# A match binder does not capture a loop-havocked local

A loop head havocs `i`, so the state past the loop carries `i` as the first
identity of the execution's range. A proof-side `match` lowers each arm against
a binder per constructor field, and when the scrutinee's constructor is known
the arm body is lifted out of the match with the binder replaced by the field.

The binder is a bound variable and `i` is free, so the two are unrelated
whatever they are called. They were called the same thing: the lowering ran
under a budget that restarted the identity counter beside the live state, so
its first binder was the same `Variable` the havoc had given `i`, and the
binder-elimination rewrite replaced `i` along with `h`. The arm body here is
`to_integer(i)`, which the rewrite turned into `to_integer(m)` — making
`i == m` provable for an arbitrary `i`.

Match binders now come from a reserved range that no execution can reach, so
the arm body's `i` survives the rewrite and the claim is refused: `i` is the
loop's arbitrary value and nothing says it is `m`.

```c filename=match_binder_captures_havocked_local.c
int32 spin(int32 n, int32 m) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "match_binder_captures_havocked_local.c";

spec enum Box { Wrap(int32) }

int32 spin(int32 n, int32 m) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0 and i <= n;
    }
    have match Box::Wrap(m) {
        Box::Wrap(h) => to_integer(i),
    } == to_integer(m) by { simp(); }
    step();
    simp();
}
```

```expect
fail: `have` failed for `match Box::Wrap(m) { Box::Wrap(h) => to_integer(i) } == to_integer(m)`
```
