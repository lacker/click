# a `return` inside an explicitly preserved loop body is a function exit

The explicit `maintain by { ... }` form of
[`a_return_inside_a_summarized_loop_body_is_a_function_exit.md`](a_return_inside_a_summarized_loop_body_is_a_function_exit.md):
the `if i == 2` arm steps to the `return 7`, the other arm closes the
invariants. The returned arm is a function exit of `f`, so `ensures result ==
5` is refused on it.

```c filename=a_return_inside_an_explicitly_preserved_loop_body_is_a_function_exit.c
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
verifying "a_return_inside_an_explicitly_preserved_loop_body_is_a_function_exit.c";

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
        initialize by close();
        maintain by {
            if i == 2 {
                step();
                step();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    close();
}
```

```expect
fail: result == 5; left side evaluated to 7
```
