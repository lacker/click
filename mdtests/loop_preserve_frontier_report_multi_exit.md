# An unfinished `preserve` lists every end still ahead of it

A loop body with a `break` and a `continue` has three ways for a path to end,
and a preservation script closes them one at a time. The frontier report a
still-unfinished script gets separates the two halves of that picture: what the
rest of the body holds ahead of *this* path, and what the script's other paths
have already closed. Both halves matter while the body is being written —
"still ahead on this path: the body's end and 1 `continue`" says which case has
not been reached, and "Already complete: 1 at a `break`" says the `break` arm
is done.

`scan` breaks at 3, continues at 5, and otherwise falls to the body's end. The
proof closes the `break` arm and steps once into the other, stopping before the
second C `if`, so exactly one of the two remaining ends is behind it.

Counting only this loop's own exits is what makes the "still ahead" list
correct: a nested loop or `switch` owns the `break`s and `continue`s written
inside it, and they are not ends of this body.

The single-exit shape, and what this report replaces, is
[`loop_preserve_frontier_report.md`](loop_preserve_frontier_report.md).

```c filename=scan.c
int32 scan(int32 n) {
    int32 i = n;

    while (i > 0) {
        if (i == 3) {
            break;
        }
        if (i == 5) {
            i = i - 1;
            continue;
        }
        i = i - 1;
    }
    return i;
}
```

```click
verifying "scan.c";

int32 scan(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            if i == 3 {
                step();
                step();
            } else {
                step();
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: stopped inside the loop body: the frontier is at statement 5, `if ((i == 5))`, after tactic 1 `step`; still ahead on this path: the body's end and 1 `continue`. Already complete: 1 at a `break`
```
