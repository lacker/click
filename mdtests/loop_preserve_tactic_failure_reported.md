# A tactic that fails inside `preserve` reports its own failure

The frontier report an unfinished `preserve` gets
([`loop_preserve_frontier_report.md`](loop_preserve_frontier_report.md)) is for
a body that ran out of *written* tactics, not for one whose tactics failed. A
tactic that cannot be checked stops the body where it stands and its own
diagnostic is what the author sees; the body never reaches the end of the
script, so the frontier report must not displace it.

`count_down`'s body is one statement and its preservation proof is complete,
except that it opens with a `have` stating something false. The report names
the tactic and the missing fact, not the loop.

```c filename=count_down.c
int32 count_down(int32 n) {
    int32 i = n;

    while (i > 0) {
        i = i - 1;
    }
    return i;
}
```

```click
verifying "count_down.c";

int32 count_down(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            have i < 0 by simp;
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: `count_down.contract` tactic 0: `have` failed
```
