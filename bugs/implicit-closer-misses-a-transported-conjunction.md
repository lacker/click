# The implicit closer misses a conjunction whose leaves need memory transport

Soundness: incomplete. Click refuses a true `ensures` that it proves when
the same claims are written as separate `ensures` or as an explicit `have`.
No false claim is accepted: the closer fails to find a proof, and the
explicit forms check the same kernel goal.

## Violated invariant

The implicit closer at a function's exit closes an `ensures` that a single
`have` of that same proposition closes at the same point. Here
`have <conjunction>;` after `step_until(function.exit)` succeeds, and the
implicit closer on the identical `ensures` fails.

## Reproduction

```rust
pub struct Pair {
    pub x: u32,
    pub y: u32,
}

pub fn copy_pair(dst: &mut Pair, src: &Pair) {
    dst.x = src.x;
    dst.y = src.y;
}
```

```click
fn crate_name::copy_pair(dst: &mut crate_name::Pair, src: &crate_name::Pair) {
    owns *dst;
    views *src;
    ensures dst.x == src.x and dst.y == src.y;
}
```

This fails with `unclosed goal: dst.x == src.x and dst.y == src.y`. Each
of these variants verifies:

- the two leaves as two `ensures` clauses;
- the proof `by { step_until(function.exit); have dst.x == src.x and dst.y == src.y; }`;
- the proof `by { step_until(function.exit); have dst.x == src.x; have dst.y == src.y; }`.

In the trace, the first leaf compares `dst.x` read at `statement(0).exit`
with `src.x` read at the exit state. Naming `dst.x` moved its read across the
store to `dst + 4`. `src.x` stays at the exit, because crossing that store
needs the stated separation of `*dst` and `*src`. The cell walk then stops
with "step not proved separate from the queried bytes", even though
`memory(dst.y) separate memory(*src)` is among the premises.
`try_direct_structural_closure_inner` splits the conjunction and closes each
leaf structurally. That closure doesn't use the stated separation, while the
`close()` a `have` runs does (`src/surface/proof/smart_closures/search.rs`,
`src/surface/proof/driver/claims.rs` `close_claim_directly_from_outcome`).

The same shape is what a whole-struct claim lowers to: `ensures *dst == *src`
is `dst.x == src.x and dst.y == src.y`. So the fixture
`design/charon-trial/generic-struct-values` proves `copy_pair` with an explicit
`have *dst == *src;`.

C at the same point closes the conjunction
(`mdtests/a_struct_equality_compares_every_field.md`).

## Acceptance criteria

- The reproduction's `ensures dst.x == src.x and dst.y == src.y` verifies
  with no proof, through the implicit closer.
- `ensures *dst == *src` verifies with no proof for the same Rust function,
  and `generic_struct_values::copy_pair` drops its explicit `have`.
- A regression keeps the conjunction and both separate-`ensures` forms, plus
  a control that copies only `x` and must fail.
- The closer's work for an `n`-leaf conjunction stays within a constant
  factor of `n` separate `ensures`, measured in deterministic work at
  several sizes.
