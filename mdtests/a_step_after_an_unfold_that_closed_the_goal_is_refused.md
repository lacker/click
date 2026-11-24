# a step after an `unfold` that closed the goal is refused by name

When the goal an `unfold` refreshes is already an available fact, the `unfold`
closes it. A later step then has nothing to prove. Before this was refused, the
script went on against the goal as written before the `unfold`, so the
`close() using` below read `0 <= w2(a, b)` with `w2` still folded. It then
reported that the listed premise, the unfolded goal verbatim, did not prove
it. Naming the step that closed the goal points at the line to delete.
`known`, a bare `close()`, and `normalize` after a closed goal remain harmless.

```click
spec enum Ctx { Top, Up(Ctx) }

function d(c: Ctx) -> Integer decreases c {
    match c { Ctx::Top => 0, Ctx::Up(u) => 1 + d(u) }
}

function w2(a: Ctx, b: Ctx) -> Integer { d(a) + d(b) }

theorem bound_through_wrapper(a: Ctx, b: Ctx) {
    requires 0 <= d(a) + d(b);
    ensures 0 <= w2(a, b) by {
        unfold(w2(a, b));
        close() using { 0 <= d(a) + d(b); };
    }
}
```

```expect
fail: `close() using` follows a goal-closing tactic: `unfold` already closed this goal
```
