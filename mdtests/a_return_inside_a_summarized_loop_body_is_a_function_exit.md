# a `return` inside a summarized loop body is a function exit

`f(5)` returns `7`: the body returns when `i == 2`. The loop rule the `loop`
tactic builds used to export only the guard-false exit, so the returned path
never reached contract certification and `ensures result == 5` verified. The
returned path is now a `Return` outcome of the loop rule, retained beside the
continuing successor and checked at the function boundary with its own value
and state.

```c filename=a_return_inside_a_summarized_loop_body_is_a_function_exit.c
int32 f(int32 n) {
    int32 i = 0;
    while (i < n) {
        if (i == 2) {
            return 7;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "a_return_inside_a_summarized_loop_body_is_a_function_exit.c";

int32 f(int32 n) {
    requires n == 5;
    ensures result == 5;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    close();
}
```

```expect
fail: result == 5; left side evaluated to 7
```
