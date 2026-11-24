# A loop exit diagnostic names the surviving resource model

The break arm retains a fact about a consumed intermediate model. The model
after the join is either active or done, so a demand for a pending count of
two can fail. The diagnostic spells that goal with `state.model`.

```c filename=program.c
void walk(int n) { while (n > 0) { break; } }
```

```click
verifying "program.c";
spec enum Walk { Active, Done }
function pending(w: Walk) -> int32 { match w { Walk::Active => 1, Walk::Done => 0, } }
resource ghost(id: int32) { field model: Walk; }
tactic stop() {
    consumes dirty: ghost(0);
    produces done: ghost(0);
    ensures pending(done.model) == 0;
} by {
    unfold(dirty);
    let done = fold(ghost(0), { model: Walk::Done });
    have pending(done.model) == 0 by {
        rewrite(done.model, Walk::Done); unfold(pending(Walk::Done)); normalize();
    }
}
void walk(int32 n) {
    owns state: ghost(0);
    requires n >= 0;
    requires state.model == Walk::Active;
    ensures n == 0 or pending(state.model) == 0;
} by {
    loop {
        owns state: ghost(0);
        decreases n;
        invariant n >= 0;
        invariant state.model == Walk::Active;
        initialize by close();
        maintain by {
            let { done: intermediate } = stop({ dirty: state });
            let { done: state } = stop({ dirty: intermediate });
            step();
        }
    }
    step();
    have not (n > 0) or pending(state.model) == 2 by close();
    close();
}
```

```expect
fail: goal: n <= 0 or pending(state.model) == 2
```
