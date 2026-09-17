# a measure that reads memory is read at both ends of the iteration

While `box->len` is below its cap the loop counts `i` toward it and moves it
away at the same rate, and at the cap it changes nothing, so an entered loop
never exits. Its invariants are inductive, so they are not what fails. The
distance `box->len - i` reads the field and the body writes it: the back-edge
ranking obligation compares the distance in the back-edge memory with the
distance in the memory the iteration started from, finds them equal on every
path, and cannot be closed. Reading the field once and treating it as a
constant bound would have accepted this loop.

```c filename=loop_decreases_rejects_a_field_that_moves.c
struct box {
    int32 len;
};

int32 chase(struct box* box) {
    int32 i;
    i = 0;
    while (i < box->len) {
        if (box->len < 1000) {
            box->len = box->len + 1;
            i = i + 1;
        }
    }
    return i;
}
```

```click
verifying "loop_decreases_rejects_a_field_that_moves.c";

int32 chase(struct box* box) {
    owns box->len;
    requires box->len >= 0 and box->len <= 1000;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        decreases box->len - i;
        invariant 0 <= i and i <= box->len and box->len <= 1000;
    }
    step();
    simp();
}
```

```expect
fail: `*(box) - i` decreases at the back edge
```
