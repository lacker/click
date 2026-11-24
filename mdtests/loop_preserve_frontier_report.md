# An unfinished `maintain` whose rest does not run reports its frontier

A preservation script may stop before the body does: the rest of the body
then runs as an omitted `maintain` runs a whole one, and each path it reaches
closes its back edge
([`preserve_runs_the_rest_of_the_body.md`](preserve_runs_the_rest_of_the_body.md)).
When the rest does not run, refusing the script with only "must execute
exactly one complete loop-body iteration" says nothing about how far the body
actually got. That refusal is kept for a body that *is* complete and wrong —
one that runs off the loop through a `return`, say — and an unfinished body
reports its frontier instead: the statement the path stands before, the
tactic that left it there, the ends still ahead of it on this path, the paths
the script has already closed, and why the rest did not run.

`walk` is the smallest shape with something ahead: its body breaks on one
value and otherwise runs two statements. The proof steps into the `else` arm
and stops one statement short, so the report names `i = (i - 1)` as the
frontier, `step` as the tactic that got there, the body's end as what is still
ahead, and the `break` path the proof already closed. The rest does not run
because `12 / i` may divide by zero once `i` reaches `0`.

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
        i = 12 / i;
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

        initialize by close();
        maintain by {
            if i == 3 {
                step();
                step();
            } else {
                step();
            }
        }
    }
    step();
    close();
}
```

```expect
fail: stopped inside the loop body: the frontier is at statement 5, `i = (i - 1)`, after tactic 1 `step`; still ahead on this path: the body's end. Already complete: 1 at a `break`
```
