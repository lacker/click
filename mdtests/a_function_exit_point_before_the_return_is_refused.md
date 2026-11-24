# A function-exit program point before the return is refused

`at(function.exit, ...)` reads the state the function returns in. Before
execution reaches the return there is no such state, so a proof step that
names it there is refused.

```c filename=early_exit_state.c
int32 is_less(uint32 a, uint32 b) {
    return a < b;
}
```

```click
verifying "early_exit_state.c";

int32 is_less(uint32 a, uint32 b) {
    ensures result == 0 or result == 1;
} by {
    have at(function.exit, a == a) by { close(); }
}
```

```expect
fail: `at(function.exit, ...)` is available only once the function has returned
```
