# A loop body that `break`s has no invariant proof

The `loop` tactic proves one complete body iteration and closes the invariants
at the back edge. A `break` leaves the body without reaching that edge, so the
preservation obligation is refused: the loop rule has no way to certify the
path as an *exit* and join it with the guard-false exit, which is what package
A17 did for the exits of a short-circuit guard.

Every exit of Linux's `__rb_insert` is a `break` — the root-blackening exit,
the black-parent exit, and both case-3 rotations — under a `while (true)` guard
that never falls out on its own, so this refusal is what stops
[`rb_insert_color.md`](rb_insert_color.md) and, after it,
`__rb_erase_color`.

The same body reaches three further refusals depending on how the proof is
written, all of them the same missing rule:

- with the default `preserve`, the loop tactic reports `step()` recorded
  statement evidence the proof object rejected: evidence was recorded after
  the trace completed`, attributed to tactic 0 rather than to the loop;
- with the `break` inside a `branch` arm, which is the shape of every `if
  (...) break;` in the kernel, the arm's `step()` reports `loop control has no
  enclosing loop`, because the arm's execution region replaces the loop-body
  region the control statement needs;
- a `continue` is refused too; see
  [`loop_body_continue_rejected.md`](loop_body_continue_rejected.md).

```c filename=break_once.c
int32 break_once(int32 n) {
    int32 i = n;

    while (i > 0) {
        break;
    }
    return i;
}
```

```click
verifying "break_once.c";

int32 break_once(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            step();
        }
    }
    step();
    simp();
}
```

```expect
fail: must execute exactly one complete loop-body iteration
```
