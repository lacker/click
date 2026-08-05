# Preserve loadability evidence in smart-have replay

## Problem

A quantified smart `have` can succeed while lowering an indexed memory
equality from the live execution/resource context, then emit a certificate
containing only `normalize()`. Ordinary replay of that certificate lowers the
same goal without the permission evidence search used and fails with a missing
`loadable` fact.

Owned-vector growth exposed this while proving that a null allocation branch
preserves every live element of a field-derived backing array. The smart tactic
reported success; its generated certificate failed immediately in the same
verification run. This is a certificate soundness/completeness boundary, not a
reason to rewrite the proof or C source.

## Invariant

Smart tactic success means its emitted simple certificate replays from the
same surface proof state. Any memory permission needed to lower the goal must
either be available identically during replay or appear as explicit replayable
evidence in the generated certificate.

Certificate generation must not rely on ambient resource access that ordinary
replay deliberately hides from a pure nested proof.

## Regression

Own a composite resource whose array base and extent are loaded through struct
fields. After materializing those fields and refining an unrelated `malloc` to
null, use smart `have` to prove a quantified equality between every live cell
and its entry-state value. Require the generated simple certificate to replay,
then require `click expand` and `click audit` to agree on the site.

## Acceptance criteria

- Search cannot report success with an unreplayable `have` certificate.
- Required loadability evidence is retained with a stable surface spelling.
- The focused regression passes under ordinary verification and expansion.
- Failure diagnostics remain bounded when the permission is genuinely absent.
- Owned-vector growth does not need a redundant C access or proof-only memory
  write to stabilize the certificate.
