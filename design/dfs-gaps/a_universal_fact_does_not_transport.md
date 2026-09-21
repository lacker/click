# a universal fact cannot be carried to another snapshot

Classification: **missing rule** (no snapshot transport for a quantified
proposition), with a **missing surface spelling** for the one-cell workaround.

`transport(P, Q)` is how a fact about memory moves from one certified snapshot
to another. It refuses a universal outright:

```text
`search.contract` tactic 4: `have` failed for `forall (k: int32) { ((0 <= k &&
k < n) => (0 <= next[k] && next[k] < n)) }`: `search.contract` proof step
source tactic 8 > have body tactic 1: unsupported proof operation `transport`
```

The source was written as the same proposition at function entry:

```click
have forall (k: int32) {
    0 <= k and k < n implies 0 <= next[k] and next[k] < n
} by {
    transport(
        at(function.entry, forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        }),
        forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        }
    );
    assumption();
}
```

The message says which operation is unsupported but not that the *shape* is
what makes it unsupported, and not what to do instead.

There is a workaround for one cell at a time, and it is four steps where one
would do. The quantified precondition can be instantiated *at the entry
snapshot*, and the resulting single-cell fact transports:

```click
have at(function.entry, 0 <= next[cur] and next[cur] < n) by {
    instantiate(at(function.entry, forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    }), cur) using { 0 <= cur; cur < n; }
    assumption();
}
have at(function.entry, 0 <= next[cur]) by {
    extract(at(function.entry, 0 <= next[cur]));
}
have at(function.entry, next[cur] < n) by {
    extract(at(function.entry, next[cur] < n));
}
transport(
    at(function.entry, next[cur]) == at(function.entry, next[cur]),
    at(function.entry, next[cur]) == next[cur]
);
have next[cur] == at(function.entry, next[cur]) by {
    rewrite(at(function.entry, next[cur]) == next[cur]);
    normalize();
}
have 0 <= next[cur] by {
    rewrite(next[cur] == at(function.entry, next[cur]));
    assumption();
}
have next[cur] < n by {
    rewrite(next[cur] == at(function.entry, next[cur]));
    assumption();
}
```

All nineteen lines verify (`mdtests/` filter
`search_terminates_by_unmarked_count`, tactics 1..11 of the preserve body).
Three of them exist only because `transport` produces the equality in the
orientation `rewrite` cannot use: `at(e, next[cur]) == next[cur]` has to be
turned round by hand before the goal `0 <= next[cur]` mentions its left side.

Two further costs of the workaround:

- A transport of the *comparison* is refused, not only of the universal:
  `transport(at(function.entry, 0 <= next[cur]), 0 <= next[cur])` reports
  `unsupported proof operation transport`. Only equalities move, so every
  order fact has to be reconstructed by rewriting a load equality.
- A `transport` written as a top-level tactic in a loop's `preserve` body
  verifies; the same `transport` inside a `have` body in the same place reports
  `unsupported proof operation transport`. That difference is not documented
  and is probably a second defect.

Intended regression: a pure-theorem-free C fixture that transports one
quantified premise across one store to a separated owned range, in one step.

## Why it blocks the search example

It is the escape route from
`a_second_universal_have_cannot_narrow_a_stated_range.md`, and it does not
work. The quantified viewability fact can be proved at the snapshot the store
produced but not at the back edge, and it cannot be moved from one to the
other, so the bundle member stays open:

```text
this loop declares `decreases`, so the bundle also has
`0 <= unmarked(visited, 0, n)` at the back edge, `unmarked(visited, 0, n)`
decreases at the back edge: `search.contract` proof step proof tactic 1:
`assumption` requires the current goal as an available semantic fact: current
goal is a universal proposition
```
