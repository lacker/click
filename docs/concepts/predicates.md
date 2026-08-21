# Predicates

A predicate gives a name to a proposition.

For example:

```click
predicate sorted_pair(p: int32[]) {
    p[0] <= p[1]
}
```

Then a contract can use:

```click
ensures sorted_pair(p) by {
    execute();
    unfold(sorted_pair);
    simp();
}
```

## Predicates Are Opaque

Predicate calls are not unfolded automatically. Click can reuse an exact
predicate fact, but it does not normally look inside a predicate unless the
proof says:

```click
unfold(sorted_pair);
```

This opacity is useful. It lets predicates act as stable abstraction boundaries
instead of being expanded everywhere.

## Predicates In Requirements

Predicates can package preconditions:

```click
predicate has_zero(p: int32[], n: int32) {
    (0..n).any(|k| { p[k] == 0 })
}

int32 find_zero(int32 p[], int32 n) {
    requires loadable(p[0..n]);
    requires present: has_zero(p, n);
    ...
}
```

If a proof needs the body of `has_zero`, unfold it and then use the resulting
facts. Existential bodies may need `choose`.

## When To Define A Predicate

Use a predicate when:

- a memory-reading precondition would otherwise be awkward,
- several contracts need the same concept,
- a loop invariant should name a larger property,
- or a proof should hide a complex proposition behind a stable name.

Avoid defining a predicate just to rename a one-line scalar fact unless the name
clarifies the proof.
