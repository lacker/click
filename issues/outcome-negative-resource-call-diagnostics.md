# Preserve resource and call failures without outcome fallbacks

## Violated invariant

False postconditions involving folded resources, opaque calls, consumed write
permissions, or grouped tactic ordering must be rejected by the typed outcome
and resource goals that own those semantics. They must not depend on the
legacy grouped/exit certifier to notice the missing resource or unproved
claim.

## Current reproductions

The 2026-08-19 census includes these representative fixtures:

- `mdtests/composite_resource_folded_nested_fact_projection.md`
- `mdtests/composite_resource_nested_observe_not_automatic.md`
- `mdtests/grouped_fold_after_simp_does_not_close.md`
- `mdtests/grouped_post_tactics_respect_order.md`
- `mdtests/grouped_unfold_respects_order.md`
- `mdtests/opaque_call_does_not_preserve_overlapping_field.md`
- `mdtests/opaque_call_rejects_weak_postcondition.md`
- `mdtests/permission_call_consumes_write_without_return.md`
- `mdtests/resource_summary_requires_returned_write.md`

The implementation must generate a per-file manifest first because reused
function labels such as `return_fd` and `identity` are not unique fixture ids.

## Intended regression

- Each missing production, observation, returned permission, or grouped claim
  remains an explicit open typed goal with a stable source-facing diagnostic.
- A negative grouped proof cannot be accepted by closing only its proposition
  siblings or padding a certificate with assumptions.
- Candidate failure publishes no resource transition or partial expansion.

## Acceptance criteria

- All classified fixtures retain their expected diagnostic substring and run
  neither outcome fallback span.
- Positive folded-resource and call siblings remain green and independently
  replay their retained certificates.
- Resource checking remains target/output-sensitive rather than eagerly
  materializing pairwise facts.
- `scripts/check.sh` passes.

