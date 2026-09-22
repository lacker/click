# Spec-carrier substitution has no binder handling: capture and silent drops

P1. A substitution must respect every binder scope it crosses.

## What was found

The core carrier's `substitute_bitvector_variable` RangeFold arm refuses
when the fold binder shadows `from` and capture-avoidingly renames colliding
binders (`src/kernel/reasoning/substitution.rs:4890-4953`). The
**spec-carrier** arms have no scope handling at all:

- `substitute_bitvector_variable_in_spec_integer`
  (`src/kernel/reasoning/substitution.rs:3590`), the
  `SpecExpression::RangeFold` arm (3295) and the `SpecExpression::Let` arm
  (3318) substitute fold/let bodies past their own binders;
- the spec quantifiers in
  `substitute_bitvector_variable_in_spec_proposition` (3411) substitute into
  `ForAll*/Exists*` bodies without capture-avoiding renames;
- the machine-backed Integer term route swallows errors:
  `substitute_bitvector_variable_in_integer` (1653) maps
  `Ok => result, Err(_) => term.clone()`, so an `UnsupportedCarrier` /
  work-limit condition makes a "substituted" proposition keep an undeleted,
  now-free occurrence of the old variable.

Machine-confirmed (same branch investigation module in
`src/kernel/reasoning/substitution.rs`):
- capture: substituting the fold's `item`-reader with a machine variable
  equal to the fold's accumulator identity leaves the fold body a captured
  `Variable(accumulator)` occurrence (`hunt_investigation_spec_fold_substitution...`);
- silent drop: the same walk left a fold body whose *own bound* occurrence
  was silently not rewritten while the rest of the term was substituted.

Callers are reachable on the proof path: the spec quantifier substitution is
used by `src/kernel/api/contract_certification/contract_claims.rs:719` and
the spec-model rewiring (`substitution.rs:4141+`), so an instantiated
instance can bind the inserted expression into the fold/quantifier scope.

## Intended regression

Two unit tests mirroring the core route's capture tests:
(a) substituting a value whose free identities collide with the fold/let/
quantifier binder renames the binder (no capture), and (b) substituting
`from` beneath its own binder leaves that scope untouched (shadow case).
The swallowed-error route must either propagate or refuse instead of
`term.clone()`.

## Acceptance

- [ ] Every spec-carrier substitution arm respects its binder scopes with
      the capture and shadow regressions in place.
- [ ] `scripts/check.sh` green.
