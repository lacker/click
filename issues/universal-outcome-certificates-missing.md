# Nested universal outcome certificates need finite case splits

Most of the original universal-certificate gap is closed: the named simple
rule `instantiate(F, value) using { ... }` specializes a universal fact at an
explicit value with guards discharged from listed premises, and certificate
lowering emits it (with `intro()` and explicit transports) for single-binder
universal goals and scalar loop-summary consequences. The mdtests
`fill3_array_loop`, `copy3_array_demo`, `fill_n_segment_invariant`,
`shifted_copy_effect_uses_covering_separate`,
`shifted_loop_effect_preserves_prefix`,
`fill_tail_rejects_tail_segment_unchanged`, and
`composite_resource_vector_fill_loop_snapshot` are no longer quarantined.

The remaining case is a **nested two-binder universal** outcome whose kernel
derivation enumerates or case-splits the bound variables:

```text
ensures sorted: sorted(p, 3);   -- forall (i) { forall (j) { ... p[i] <= p[j] } }
```

Smart reasoning proves it (finite ranges over `i`, `j` with per-case
discharge from two loop-exit `all_le_range` invariants), but the certificate
vocabulary has no expression for the case analysis: a single
`intro(); intro(); instantiate(...)` chain covers only one uniform body
discharge, and the kernel rules `FiniteForAll` / `UpperBoundSplit` /
`FiniteContextSplit` have no surface lowering. In the same test, loop-exit
universal invariant facts also fail to receive outcome surface spellings
("expressible path facts do not replay the postcondition derivation").

## Reproduction

```sh
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=bubble_sort3_two_pass_sorted cargo test --test mdtests
```

`bubble_pass3_max_suffix.md` is quarantined under this issue for the same
remainder: its grouped transition's universal loop-summary goal reports
"expressible path facts do not replay the postcondition derivation" because
the loop-exit universal invariant facts have no outcome surface spelling.

## Acceptance criteria

- `bubble_sort3_two_pass_sorted.md` and `bubble_pass3_max_suffix.md` pass
  and leave quarantine.
- The expansion of the nested universal postcondition contains only named
  simple steps (binder intros, explicit case tactics such as proof-level
  `if`, `instantiate ... using`, transports, and named theorems) and replays.
- No quantifier instantiation search runs during simple replay; every
  case in the certificate is spelled explicitly.
