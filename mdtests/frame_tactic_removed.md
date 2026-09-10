# The `frame` tactic is a parse error

Ownership bounds a function's writes at every store, so there is no separate
framing claim left for a tactic to close.

```c filename=frame_tactic_removed.c
int32 frame_tactic_removed(int32* cell) {
    cell[0] = 1;
    return 0;
}
```

```click
verifying "frame_tactic_removed.c";

int32 frame_tactic_removed(int32* cell) {
    owns cell[0..1];
    ensures result == 0;
} by {
    step();
    step();
    frame();
    simp();
}
```

```expect
fail: `frame` was removed; ownership frames untouched memory with no tactic
```
