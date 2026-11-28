# An unfold leaves an available goal open for further proof steps

Unfolding the wrapper refreshes the goal to the exact available premise.
The following `have` and explicit closer still run against the refreshed proof.

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
        have 0 <= d(a) + d(b) by close();
        close() using { 0 <= d(a) + d(b); };
    }
}
```

```expect
pass
```
