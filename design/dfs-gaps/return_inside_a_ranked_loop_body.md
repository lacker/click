# a `return` inside a loop body is not one of the loop's endings

Resolved on 2026-09-22. A function return now completes that preservation path
without running the proof-level `if`'s shared continuation or requiring the
loop invariant and ranking bundle. The continuing arm still reaches the back
edge and closes that bundle. Both an explicit proof-level `if` and automatic
preservation are covered by `mdtests/return_inside_ranked_loop_body.md`.

The remainder records the pre-fix behavior that motivated the regression.

A C loop body that leaves the function directly is ordinary C — it is the first
statement of the checked search in
`mdtests/search_terminates_by_unmarked_count.md`:

```c
while (visited[cur] == 0) {
    if (cur == to) return 1;
    visited[cur] = 1;
    cur = next[cur];
}
```

The loop rule knows three endings. `docs/reference/tactics/index.md` says a
body path must reach "the body's end, a `continue`, or a `break`", and
`mdtests/loop_body_break_exit.md` is the worked `break` case, proved with a
proof-level `if` per C `if`. Written that way, a returning path is refused
plainly:

```text
`scan.contract` must execute exactly one complete loop-body iteration, ending
at the body's end, a `continue`, or a `break`
```

That message is good: it names the rule and the three endings. What it does not
say is that `return` is deliberately absent rather than merely unspelled, and
`docs/concepts/loops-and-invariants.md` does not mention the case either.

Minimal repro of the refusal:

```c filename=zz_probe5.c
int32 scan(int32 *b, int32 n, int32 to) {
    for (int32 i = 0; i < n; i++) {
        if (i == to) return 1;
        b[i] = 1;
    }
    return 0;
}
```

```click
verifying "zz_probe5.c";

int32 scan(int32 *b, int32 n, int32 to) {
    owns b[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        owns b[0..n];
        initialize by { simp(); }
        preserve by {
            if i == to {
                step();
                step();
            } else {
                step();
                step();
                step();
                close_invariants();
            }
        }
    }
    execute();
    simp();
}
```

Omitting both phases and letting the `loop` keyword's automation walk the body
is refused too, and here the message is attributed to the wrong tactic:

```text
`scan.contract` tactic 0: `smart step selection` cannot run after execution
already reached function exit
```

Tactic 0 is the first `step()` before the loop, which has nothing to do with
it.

## `branch` does accept a returning arm, unpredictably

`branch { then { execute(); } else { } }` is the shape that works — the table
says a branch proves "every feasible arm" and joins "nonreturning arms" — but
whether it works depends on an unrelated fact being in the context first. On
the same probe it is refused with no information at all:

```text
`scan.contract` tactic 0: `branch` did not verify as a checked preservation
operation
```

No goal, no missing premise, no target, and the tactic index is again the
`step()` before the loop. Adding an unrelated quantified invariant does not
change it.

In the saved search proof the same `branch` verified only when
`have 0 <= next[cur] and next[cur] < n` — instantiated from a current-snapshot
quantified invariant — is available before it. Deriving the identical two
facts through `at(function.entry, ...)` and `rewrite` (see
`a_universal_fact_does_not_transport.md`) is not enough, and neither is
`have 0 <= next[cur] and next[cur] < n by { split(); }` over them. So the
example cannot drop the quantified invariant that
`a_second_universal_have_cannot_narrow_a_stated_range.md` makes unprovable at
the back edge, and the two gaps close the circle.

Intended regression: the `scan` fixture above with `expect pass`, proved with
the documented proof-level `if`; and a `branch` refusal that names what the
preservation operation could not establish.
