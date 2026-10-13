# `old(result)` is refused

`result` is the return value; it does not exist at function entry, so
`old(result)` has no meaning. It is refused when the contract is read instead
of silently meaning the same as `result`.

```c filename=old_result.c
int h(int x) { x = 5; return x; }
```

```click
verifying "old_result.c";

int h(int x) {
    ensures old(result) == 5 by { execute(); simp(); }
}
```

```expect
fail: `result` cannot be named inside `old(...)`
```
