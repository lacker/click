# by names a tactic missing its call

Every tactic after `by` is written with its parentheses. A
tactic name without its call is refused with the spelling to write.

```click
theorem missing_call(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by close;
}
```

```expect
fail: close` requires parentheses
```
