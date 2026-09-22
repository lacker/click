# store_union leaves a stale raw cell under an equal spelling of the address

P1. A union overlay outranks the raw cell at *the address*, not at one
spelling of it.

## Invariant

`store_union` (`src/kernel/primitives/memory_state.rs:2497`) removes
`self.cells[pointer]` and inserts the overlay, both keyed by the exact
pointer spelling it was handed. The class invariant asserted in that file
("store_with_context and store_union keep the two disjoint at every pointer")
is therefore only kept for one spelling at a time: a raw scalar cell stored
through a proven-equal alias spelling (a contract-returned pointer, e.g.
`ensures result == p`) of the same address survives beside the overlay,
under the other spelling. The copy paths that read `known_value` at an
aliased spelling (`src/kernel/functions.rs` `copy_aggregate_union_member` /
`uninitialized_aggregate_copy_source_cell`, around lines 11093 and 11330)
then copy the stale scalar instead of the union member stored over it.

Machine-confirmed on the `claude/soundness-hunt-phase2` investigation branch:
`retire_investigation_store_union_keeps_aliased_raw_cell` stores a raw cell
at the alias spelling, then a `Int16` overlay under the base spelling, and
`known_value` at the alias spelling still answers the stale cell beside
`has_union_overlay_at(base) == true`.

## Intended regression

The same kernel-level scenario as a regression: for a proven-equal pair
(raw cell at the alias spelling, overlay under the base spelling), the
memory's per-address state must be inconsistent — either both spellings are
dropped (`without_possible_aliasing_cells` consults the facts) or whichever
store happens last wins at *both* spellings. Passing the given facts context
(`store_union` has none today) is one repair; extending the exactly-equal
spelling machinery is another. Free choice: the acceptance criterion below.

## Acceptance

- [ ] A raw cell and a union overlay that provably name one address cannot
      both be expected to answer at once, whichever of the two spellings each
      load uses.
- [ ] `scripts/check.sh` green with the regression added.
