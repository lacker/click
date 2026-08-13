# Post-execution `simp` proves a resource fact with no simple certificate

`mdtests/field_derived_precise_effect_after_metadata_write.md` fails its
`buffer_push` contract at `have 0 <= owner->len by simp;`:

```text
`buffer_push.contract` path 0, tactic 2: `have` failed: post-execution
simplification proved `0 <= owner->len`, but Click has no explicit simple
certificate for that derivation
```

Reproduce with:

```sh
MDTEST_FILTER=field_derived_precise_effect_after_metadata_write cargo test --test mdtests
```

The goal restates the `fact 0 <= owner->len` carried by the unfolded
`owned_buffer(owner)` resource, after `execute()` has written `owner->len`.
Restricted simplification finds a proof and then cannot lower it, so the
failure is certificate vocabulary, not proof strength. The reported premises
are statement-entry spellings of the length and capacity order facts plus the
entry separation fact, which suggests the derivation is reconstructing the
post-store length relation from execution history rather than from a named
transport of the resource fact across the store.

This is the failure class `issues/README.md` requires tracking: a search
reports success without a replayable certificate.

## Provenance

`git bisect` between `3c3c9a97` (good) and `e4582c18` (bad) names
`39e8af4c` "Improve verifier stability and profiling" (2026-08-12, 31 files,
+2250/-791) as the first bad commit; its parent `ae64192a` is good. The break
went unnoticed for 54 commits because nothing enforced the fixture gates. The
mdtest is quarantined in `tests/mdtests.rs` so the suite is a meaningful gate
again; un-quarantine it as part of the fix.

## Regression design

Keep the unchanged mdtest as the regression: the same C, the same resource
declaration, and the same `have 0 <= owner->len by simp;`. Do not weaken the
claim, respell the fact, or replace `simp` with a hand-written chain in order
to close the issue — the point is that this derivation must be expressible.

Distinguish the two failure modes explicitly, as the neighbouring restricted
simplification work does: failing to lower a proved goal must report
differently from failing to prove it.

## Acceptance criteria

- The mdtest passes unquarantined, with its C and claims unchanged.
- The accepted proof is an explicit simple certificate that replays; the goal
  is not proved from ambient execution history.
- `click profile`, `click expand`, and `click audit` agree about the site.
- If the certificate needs new vocabulary, it is the smallest named simple rule
  that expresses this transport, with its own focused regression.
