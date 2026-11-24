# A natural goto exit cannot hide a false return contract

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
    return 7;
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
    close();
}
```

```expect
fail: closes the outcome claims at function exit and does not execute
```
