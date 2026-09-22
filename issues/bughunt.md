# Complete the kernel soundness bug hunt

P1. Click must not accept a false contract. These reviews were discovered
while working on the DFS example, but they are verifier-wide and are tracked
separately so feature work and soundness review do not share one issue.

## Invariant

Memory, arithmetic, and control-flow rules must require the evidence their
conclusions depend on. In particular, differently spelled pointer blocks are
not separate unless `PointerBlock::proven_distinct` or checked assumptions say
so; cached memory cells are incomplete knowledge rather than a complete write
history; and machine integers may not be silently read as mathematical or
unsigned values.

Cost evidence comes from deterministic work reported by `click profile`, not
development-machine wall time.

## Open reviews

1. **Heap-allocation containment compares block spellings.**
   `heap_allocation_may_contain_pointer` in
   `src/kernel/primitives/memory_state.rs` returns false whenever
   `base.block != pointer.block`. That is stronger than
   `PointerBlock::proven_distinct`: an unresolved or contract-returned pointer
   can equal an allocation while retaining another block spelling. The helper
   feeds freeing, liveness, initialization, implicit-zero, deallocation,
   path-availability, and contract-certification decisions.

   Intended regression: two pointers with different, not-proven-distinct block
   identities are known equal; retiring the allocation through one identity
   must make loads through the other unavailable and must not retain a cached
   cell or zeroed status. A pointer into a structurally fresh, proven-distinct
   allocation remains unaffected.

2. **One-element byte-gap direction and wrapping range-fold shortcut.**
   `one_element_gap_separates_bytes` derives a direction from residue indexes,
   although its `Separate` result does not depend on that direction.
   `range_fold`'s one-step shortcut in `term_operations.rs` uses wrapping
   addition, so `i32::MAX .. i32::MIN` appears to unroll once. The latter has
   been judged unreachable because surface `(a..b).fold` lowers to the signed
   `Integer` carrier, but the rule and every direct kernel caller still need a
   written argument or a checked regression.

3. **Machine-integer and pointer edge cases need their soundness arguments
   retained at the deciding rules.** Eighteen small checks found no false
   theorem for `uint32` arithmetic/order, signed/unsigned comparison, oversized
   shifts, `INT_MIN % -1`, `uint32` to `int32` conversion, cross-object pointer
   order/subtraction, or unsigned decreases. Record why the deciding rules are
   sound and keep the existing refusals distinct from missing language support:
   `uint8`/`uint16` assignment wrapping is not modelled, and `int8` is outside
   the subset.

4. **Trust boundaries remain explicit.** `apply` requirement checks, including
   range extent guards, are enforced at
   `instantiate_theorem_application_with_assumptions`; a top-level
   `owns`/`views` extent is an environment assumption; and `import` assumes the
   imported proof. Keep these boundaries documented and covered where they are
   enforced.

## Recurring review hazards

- `Bitvector32Term::as_const` is unsigned; signed `int32` order uses
  `signed_bitvector_constant`.
- Index arithmetic wraps at 32 bits; pointer byte offsets are exact `i64`.
- Different addresses do not imply disjoint byte intervals; use
  `access_byte_overlap`.
- Missing cached cells do not prove that no write occurred; use recorded
  memory history.
- Pointer block names are not separation evidence; use
  `PointerBlock::proven_distinct`.
- Fresh identifiers must come from a range owned by their producer.
- Control-flow walks must not silently stop checking after `switch` or `break`.

## Recently completed reviews

- Memory-effect summaries now retain write widths, and load resolution requires
  the stored and requested widths to agree.
- Separation clauses carry checked range-validity bounds.
- Ancestor snapshot load naming, quantified viewability transport, and
  unrelated-snapshot comparison have been reviewed and repaired. The latter
  now compares forgotten-source identity, observable objects, heap lifetime
  and initialization metadata, and observable cells.
- Automatic-storage retirement, aggregate parameter values, offset aliasing,
  and symbolic population-count overflow have focused regressions.

## Related tooling observations

- The CLI surface-depth boundary tests run within 0.5% of the gate's 8 MiB
  stack. Keep new `CMemory` state behind an existing pointer.
- `cargo test --lib` can fail
  `targeted_simple_verification_does_not_verify_unrelated_theorems` when tests
  share a process; `scripts/check.sh` remains the gate.
- Unit tests outside the gate need `RUST_MIN_STACK=8388608`.
- The C0 parser panics instead of refusing `int32* tab[2];` at file scope.
- Some pointer-field and dangling-use diagnostics still omit the relevant
  object or source name.

## Acceptance

Each open review is either repaired with focused negative and positive
regressions, or documented as sound at the deciding rule with coverage that
exercises the disputed boundary. Remove completed items from this issue; delete
the issue and its P1 index entry when none remain.
