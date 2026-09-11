# Reduce repeated work in deeply nested `Integer` quantifiers

P2: a deferred tooling-scaling problem in an otherwise implemented
`Integer` quantifier path. The current checked universal-introduction path
freshens, substitutes, and copies the remaining proposition body at every
`intro()`, producing quadratic work for `n` nested binders. This is a known,
user-approved deferral; it is not evidence that quantifier soundness may be
weakened or that budgets may be raised.

## Current reproduction and violated invariant

The source regressions `mdtests/integer_forall_intro.md`,
`mdtests/integer_forall_intro_have.md`,
`mdtests/integer_forall_logical_have.md`, and
`mdtests/integer_quantifier_shadow_does_not_reuse_requirement.md` exercise the
implemented `Integer` universal-introduction, nested-proof, and capture
boundary. The corresponding implementation paths are
`src/kernel/proof/object.rs`'s `ProofObject::apply_intro`,
`src/kernel/proof/facts.rs`'s `ProofFacts::freshen_integer_forall_body`,
the capture-avoiding walker in `src/kernel/reasoning/substitution.rs`, and
the shared fresh-variable logic in `src/kernel/primitives.rs`. The existing
kernel regression `intro_freshens_a_universal_binder_away_from_ambient_facts`
in `src/kernel/proof/object.rs` is the bound/free collision anchor. Preserve
these checked paths while reducing repeated proposition copying.

A reduced freshening measurement historically recorded deterministic work
lower bounds at depths 8, 16, 32, and 64 of
122, 370, 1250, and 4546 units. The measurements include empty assumptions
and an ambient quantified tautology with overlapping binder identities. They
measure only the freshening helper; unrelated proof-state and Surface
statement copying is excluded. This is a synthetic stress test; no realistic
`Integer` proof workload has yet been identified as impractical because of
this nesting. Rebuild a complete checked-introduction measurement against
the current implementation before treating the curve as a regression result;
do not assume the historical harness is still committed unchanged.

The invariant is that capture-avoiding substitution, freshening, complete
carrier environments, and checked certificates remain sound while work for a
selected proof scales approximately linearly, up to logarithmic indexing
factors, in the source and certificate. Freshening must cover introduced and
captured `Integer` identities, including ambient bound/free collisions; it
must never reuse an ambient same-numbered variable to prove a universal claim.

## Intended regression

Retain a complete checked source regression at depths 8, 16, 32, and 64 with
empty assumptions and with an ambient quantified fact whose binder identities
overlap the introduced binders. Include nested universal introduction,
`have`, and theorem-application/expansion followed by independent
re-verification. Include an explicit certificate and a large unrelated
checker context so a fix cannot merely move repeated work elsewhere or
optimize only fresh-variable search.

## Acceptance criteria

- The complete checked path has deterministic multi-size work that is
  approximately linear, up to logarithmic indexing factors, in selected
  source and certificate size; the 8/16/32/64 counts remain recorded as
  lower-bound history, not as a performance target.
- Tests cover empty assumptions, ambient bound/free-variable collisions,
  C/`Integer` shadowing, nested binders, shared replacements, expansion, and
  independent re-verification. No test bypasses validation or soundness
  checks.
- Immutable proposition sharing or deferred substitution may be used, but
  every binder mapping, carrier, definedness obligation, and certificate
  premise remains independently checked. A sparse or colliding identity must
  fail safely rather than capture an unrelated variable.
- Freshening and substitution do not clone unrelated checker state or scan
  the whole environment per binder. Memory cleanup remains bounded and live
  shared bodies are not retained indefinitely.
- The focused regressions and `scripts/check.sh` pass, with no claim that a
  realistic workload currently blocks shipping the implemented quantifier
  feature.
