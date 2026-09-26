# an undefined loop guard is spelled in words

`a + b` may overflow, so the guard has no value on some path and the loop is
refused. The refusal used to name the undefined behavior by the kernel's
variant,

```text
the loop condition could not be evaluated on this path: it reaches undefined behavior (SignedOverflow)
```

and now says what happened in the words every other undefined-behavior
refusal uses.

```c filename=an_undefined_loop_guard_is_spelled_in_words.c
int32 f(int32 a, int32 b) {
    while (a + b > 0) {
        a = 0;
        b = 0;
    }
    return a;
}
```

```click
verifying "an_undefined_loop_guard_is_spelled_in_words.c";

int32 f(int32 a, int32 b) {
    requires a <= 0;
    ensures result <= 0;
} by {
    loop {
        invariant a <= 0;
    }
    step();
    simp();
}
```

```expect
fail: `f.loop(0).preserve`: the loop condition could not be evaluated on this path: it reaches undefined behavior (signed overflow)
```
