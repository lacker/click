# `loop` proves a natural `goto` cycle with a named exit

The existing `loop` keyword also covers a cycle with one checked forward exit
edge. The back edge re-enters `again`; the forward edge resumes at `done`.

```c filename=natural_goto_exit_label.c
int32 count_down(int32 n) {
again:
    if (n == 0)
        goto done;
    n--;
    goto again;
done:
    return 0;
}
```

```click
verifying "natural_goto_exit_label.c";

int32 count_down(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        invariant n >= 0;
        decreases n;
    }
    simp();
}
```

```expect
pass
```
