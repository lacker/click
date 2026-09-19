# pure theorem rejects resource requirements

This checks that theorem declarations stay pure: a theorem cannot take a
resource from the caller's resource context. Applying a theorem lends nothing,
consumes nothing, and separates nothing, so `owns` and `consumes` have nothing
to take and nothing to give back.

One resource clause does have a reading without an owner. `views v[lo..hi];`
states that reads of the range are defined, which is an ordinary hypothesis, and
a theorem accepts it — see
`mdtests/theorem_views_states_a_readable_range.md`. The refusal points there,
because a reader who wrote `owns` over a range they only read wanted that
clause.

```click
theorem resource_requirement_is_not_pure(p: int32*) {
    consumes p[0..1];

    ensures 0 == 0 by auto;
}
```

```expect
fail: pure theorem `resource_requirement_is_not_pure` cannot require a resource: applying a theorem lends, consumes and separates nothing. A theorem states that a range is readable with `views v[lo..hi];`, which its proof assumes and anyone who applies it owes
```
