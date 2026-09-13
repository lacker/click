# An unfinished `preserve` reports the frontier it reached

A preservation script is written a few tactics at a time, and until its last
path reaches one of the body's ends it is unfinished. Refusing it with only
"must execute exactly one complete loop-body iteration" says nothing about how
far the body actually got, so the author gets no signal at all until the whole
body verifies end to end. That refusal is kept for a body that *is* complete
and wrong — one that runs off the loop through a `return`, say — and an
unfinished body reports its frontier instead: the statement the path stands
before, the tactic that left it there, the ends still ahead of it on this path,
and the paths the script has already closed.

`walk` is the smallest shape with something ahead: its body breaks on one
value and otherwise runs two statements. The proof steps into the `else` arm
and stops one statement short, so the report names `i = (i - 1)` as the
frontier, `step` as the tactic that got there, the body's end as what is still
ahead, and the `break` path the proof already closed.

A tactic that fails inside the body reports its own failure, not this one
([`loop_preserve_tactic_failure_reported.md`](loop_preserve_tactic_failure_reported.md)),
and a body with more than one kind of exit left open lists each of them
([`loop_preserve_frontier_report_multi_exit.md`](loop_preserve_frontier_report_multi_exit.md)).

```c filename=walk.c
int32 walk(int32 n) {
    int32 i = n;

    while (i > 0) {
        if (i == 3) {
            break;
        }
        i = i - 1;
        i = i + 0;
    }
    return i;
}
```

```click
verifying "walk.c";

int32 walk(int32 n) {
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
fail: stopped inside the loop body: the frontier is at statement 5, `i = (i - 1)`, after tactic 1 `step`; still ahead on this path: the body's end. Already complete: 1 at a `break`
```
