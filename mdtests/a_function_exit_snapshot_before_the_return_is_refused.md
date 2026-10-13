# A function-exit snapshot before the return is refused

`at(function.exit, ...)` reads the state the function returns in. Before
execution reaches the return there is no such state, so a proof step that
names it there is refused.

```c filename=early_exit_snapshot.c
int32 is_less(uint32 a, uint32 b) {
    return a < b;
}
```

```click
verifying "early_exit_snapshot.c";

int32 is_less(uint32 a, uint32 b) {
    ensures result == 0 or result == 1;
} by {
    have at(function.exit, a == a) by { simp(); }
    execute();
    simp();
}
```

```expect
fail: `at(function.exit, ...)` is available only once the function has returned
```
