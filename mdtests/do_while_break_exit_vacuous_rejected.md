# A `do ... while` claim only one exit supports is refused

The negative sibling of
[`do_while_break_exit_join.md`](do_while_break_exit_join.md). The C returns `0`
whenever `i` is not `3` on the first visit, so `result == 3` is false; it used
to verify, because the loop exported no guard-false exit and the `break` exit
was the only way out the successor knew about.

```c filename=do_break.c
int32 do_break(int32 n) {
    int32 i = n;
    do {
        if (i == 3) break;
        i = 0;
    } while (i > 0);
    return i;
}
```

```click
verifying "do_break.c";

int32 do_break(int32 n) {
    requires n >= 0;
    ensures result == 3;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
    }
    step();
    simp();
}
```

```expect
fail: unclosed goal: result == 3
```
