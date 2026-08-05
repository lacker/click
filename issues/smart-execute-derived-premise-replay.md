# Replay assumption-derived premises selected by `execute`

## Problem

While composing owned-vector growth, `execute()` found the arithmetic premise
`owner->len <= owner->cap + 1` from the resource facts
`owner->len <= owner->cap` and `1 <= owner->cap`. Search advanced through the
opaque copy call, but certificate construction then rejected that same proof:

```text
execute used an assumption-derived theorem premise without a replayable derivation
```

A smart tactic must not report an internal success that its certificate path
cannot replay. Adding a surface `have` for the derived inequality makes this
particular proof proceed, but would hide a tooling inconsistency and force
proof scripts to restate routine consequences at unpredictable call sites.

## Invariant

Every premise selected by smart execution must have one deterministic outcome:

- emit and replay a checked proposition derivation;
- use an exact listed surface premise; or
- reject the candidate during search before advancing the execution frontier.

Search-only contextual consequences must never reach certificate construction
as unaccounted theorem premises.

## Regression

Use an opaque helper requiring `length <= destination_capacity`. Give the
caller exact facts `length <= old_capacity` and
`destination_capacity == old_capacity + 1`, then let `execute()` derive the
helper requirement. Expansion must produce a simple certificate that verifies
again without requiring the author to insert the derived inequality manually.

## Acceptance criteria

- `execute()` and its emitted certificate agree on the derived call premise.
- `click expand` verifies the expanded proof and reaches a fixed point.
- The fix is general proposition-derivation plumbing, not a vector-specific
  arithmetic rule.
- Failed candidates remain within the smart-tactic budget and diagnostics name
  the surface obligation rather than dumping the kernel state.
