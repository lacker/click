# observe after function exit says to move it

`observe` reads a resource at the execution frontier. After `step_until(function.exit)` reaches the exit there is none, and the refusal says so instead of reporting an unsupported proof shape.

```c filename=observe_after_function_exit_says_to_move_it.c
int f(int *p) { return p[0]; }
```

```click
resource cell1(p: int32*) {
    owns p[0..1];
    fact p[0] >= 0;
}

verifying "observe_after_function_exit_says_to_move_it.c";

int32 f(int32* p) {
    owns cell1(p);
    ensures result >= 0;
} by {
    step_until(function.exit);
    observe(cell1(p));
    close();
}
```

```expect
fail: `observe(cell1(p))` must run before execution reaches function exit
```
