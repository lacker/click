# Make `arithmetic` a smart tactic with an explicit certificate

## Violated invariant

The kernel checks an explicitly chosen derivation; it does not reconstruct a
nontrivial derivation hidden behind one apparently simple proof step. A surface
smart tactic may inspect the current goal and named premises, choose arithmetic
bounds and rules, and emit a certificate. Kernel work should then be a linear
sequence of local checks whose cost and completeness are determined by that
certificate.

`arithmetic()` is currently classified as a simple tactic, but its kernel
operation is a small arithmetic decision procedure. The surface step names the
premises and goal, not the derivation between them. The kernel normalizes
expressions, combines inequalities, reconstructs intervals for nonlinear and
bitwise terms, checks signed-overflow side conditions, and decides whether the
goal follows. That reasoning is deterministic and restricted to explicit
inputs, so it is not ambient proof search, but it hides substantially more
planning than the name "simple tactic" suggests.

The intended design is for `arithmetic()` to become a smart tactic. Planning
belongs in the surface layer, while the kernel retains only explicit, local
arithmetic-certificate rules.

## Current behavior

The surface syntax is:

```click
arithmetic();
arithmetic() using {
    0 <= x;
    x <= 10;
}
```

`ProofTactic::ArithmeticUsing` and `ProofStep::ArithmeticUsing` are classified
as `TacticClass::Simple(SimpleTactic::Arithmetic)`. Applying the step lowers
the listed propositions, checks that each is exactly available, and calls
`KernelProof::apply_arithmetic`. That invokes
`check_signed_affine_arithmetic` in
`src/kernel/proof/fact_reasoning.rs`.

The listed propositions are the entire premise universe, which is an important
and desirable restriction. Nevertheless, the single kernel call currently
performs all of the following work without an explicit derivation payload:

- recognizes and normalizes signed affine equalities, disequalities, and
  inequalities;
- establishes signed-`int32` definedness for affine goal expressions;
- accepts an identical normalized inequality or sums all selected inequalities
  with coefficient one, with explicit premise repetition representing a larger
  positive coefficient;
- extracts lower and upper bounds for canonical atomic terms from those
  inequalities;
- recursively propagates conservative intervals through supported products,
  constant remainder, constant left and arithmetic-right shifts, and masked
  bitwise-and expressions;
- checks every relevant intermediate signed operation for overflow or another
  C undefined-behavior condition; and
- compares the resulting endpoint intervals, including a special
  shared-operand rule for arithmetic right shift.

The interval reconstruction is capped by
`ARITHMETIC_INTERVAL_DEPTH = 32`. `signed_term_interval` silently returns no
interval beyond that depth, so otherwise supported proofs depend on an opaque
nesting limit. This was initially listed as a structural cleanup in
`issues/simplify-kernel.md`. Merely replacing the recursion with an iterative
walk would make that hidden decision procedure complete over its input, but it
would invest in machinery that this issue intends to remove from the kernel.
The limit is therefore tracked here and should normally disappear as part of
the certificate migration rather than receive an independent rewrite.

The surface is already partly acting as a planner:
`src/surface/proof/surface_certificates.rs` and
`src/surface/proof/pure_theorems.rs` call the kernel arithmetic checker to test
whether an `ArithmeticUsing` step will succeed. This coupling should be
reversed. Surface planning should own the arithmetic algorithm and produce the
evidence consumed by the kernel, rather than calling the authoritative checker
as a planning oracle.

## Intended regression

Add a proof whose supported signed-arithmetic expression is nested more than
32 levels deep. Its surface arithmetic planner should produce an explicit
certificate, and checking that certificate should succeed with deterministic
work proportional to the expression and certificate sizes.

Add a neighboring proof with an overflowing intermediate signed operation deep
in the expression. Planning must not produce a successful certificate, and a
hand-constructed or tampered certificate claiming that interval must be
rejected locally by the kernel. This ensures that moving planning out of the
kernel does not weaken C undefined-behavior checks.

## Proposed certificate boundary

Keep the user-facing `arithmetic()` syntax if it remains useful, but classify
it as smart and expand it before authoritative checking. The expansion may be
a sequence of explicit simple proof steps or a typed arithmetic certificate;
it does not need to expose every implementation detail as a pleasant
handwritten tactic. In either representation, the evidence must name the
chosen route so the kernel never has to rediscover it.

A likely certificate has three layers:

1. **Premise references.** Refer to positions in the exact surface-supplied
   premise list. Kernel application continues to require every referenced
   proposition to be exactly available; there is no ambient fact search.
2. **Local derivation nodes.** Record affine normalization/combination steps
   and bottom-up interval steps. Each interval node identifies its term,
   child-node references, derived endpoints, and rule such as constant, atomic
   bound, add, subtract, multiply, remainder, shift, or mask. The kernel checks
   the node from only its referenced inputs, including intermediate overflow
   and definedness.
3. **Conclusion.** Record the final equality, disequality, or signed-order
   comparison justified by normalized affine evidence or interval endpoints.

The exact representation remains a design decision. A flat, topologically
ordered vector is attractive because it permits iterative linear checking,
avoids Rust call-stack dependence, makes references easy to validate, and can
share repeated subexpressions without requiring the checker to hash deep terms.
A tree is simpler but can duplicate work and recreate stack-depth concerns.

Affine certificates need an explicit account of which inequalities are
combined and with what nonnegative coefficients. Preserving today's syntax
does not require preserving the current implementation restriction that every
listed inequality has coefficient one and larger coefficients are spelled by
repetition, but changing that behavior is optional. The first migration should
prefer semantic compatibility unless a more general coefficient payload makes
the checker materially simpler.

Interval rules should initially preserve exactly the existing supported
fragment. Adding division, logical shift, conditionals, additional bitwise
operations, or wider integer reasoning is a separate feature decision. In
particular:

- all intermediate signed operations must remain proven defined, not merely
  the final result;
- the bitwise-and rule must retain its current operand-definedness check even
  though the result interval is determined by the constant mask;
- unsupported operators should fail planning promptly rather than trigger a
  broader search; and
- atomic bounds should be tied to explicit premise evidence, not recovered by
  scanning ambient facts.

Existing named standard arithmetic theorems are useful expansion targets for
common cases, and current `simp` expansion already prefers several of them.
They do not cover the full behavior of `arithmetic`, especially general affine
combination and bounded nonlinear operations, so this migration cannot simply
replace every arithmetic step with the current theorem catalog. Either add a
small set of general certificate primitives or deliberately enlarge that
catalog without turning it into an enumeration of expression shapes.

## Design decisions

Resolve these before implementation:

- Whether the explicit checked representation is a new typed certificate
  payload, new source-printable simple tactics, or a combination where the
  smart surface tactic prints a compact certificate form.
- Whether affine evidence carries arbitrary nonnegative coefficients or
  preserves premise repetition as the coefficient language.
- Whether certificate nodes carry claimed endpoint values for direct checking
  or let each local rule compute its result from child endpoints. Either is
  sound if the term/rule relationship is checked; carrying endpoints generally
  improves diagnostics and tamper tests.
- How expansion and profiling present one user `arithmetic()` invocation and
  its potentially many certificate nodes without producing an unreadable
  source dump.
- Whether query-local sharing is worth representing. Do not add a cache keyed
  by deep structural term comparison on a hot path merely to deduplicate a
  tree that is already explicit and acceptably sized.

None of these decisions requires retaining the existing kernel decision
procedure or its depth limit.

## Acceptance criteria

- `arithmetic()` is classified and implemented as surface planning, not as a
  simple kernel tactic that reconstructs an omitted derivation.
- Successful arithmetic planning produces explicit evidence that can be
  inspected, serialized with the proof representation, and checked without
  calling the planner again.
- The kernel checker uses only the goal, explicitly referenced premises, and
  certificate nodes. It performs no ambient fact selection, recursive proof
  attempts, or alternate derivation search.
- `check_signed_affine_arithmetic`, `signed_term_interval`, and
  `ARITHMETIC_INTERVAL_DEPTH` are deleted from the kernel, or reduced to
  clearly local certificate-rule checks with no whole-goal planning role.
- Existing affine, bounded-product, remainder, shift, mask, equality, and
  signed-overflow acceptance/rejection behavior remains covered.
- A certificate with a changed premise reference, term, operator, endpoint,
  coefficient, child reference, or final comparison is rejected.
- Deep supported expressions no longer fail at an opaque nesting depth, and
  checker implementation is iterative wherever certificate depth could exhaust
  the Rust stack.
- Multi-size deterministic regressions demonstrate checker work near-linear in
  the explicit expression and certificate sizes. Unrelated ambient facts do
  not change that curve.
- `click expand`, ordinary verification, profiling, and audit agree on the
  expanded arithmetic proof and successfully recheck it.
- User documentation describes `arithmetic` as smart, its supported fragment,
  its exact-premise behavior, and its expansion/failure diagnostics.

## Non-goals

- Extending Click's supported arithmetic operators or integer widths.
- Searching the ambient context for useful inequalities.
- Replacing arithmetic reasoning with an SMT solver inside the kernel.
- Weakening signed-overflow or other C undefined-behavior checks.
- Preserving compatibility for low-level internal kernel APIs; Click currently
  has no such compatibility commitment.

## Suggested implementation order

1. Specify the typed certificate and local checking rules with direct unit
   tests, including malformed and tampered certificates.
2. Move affine and interval planning into the surface layer and have it produce
   the certificate from the exact listed premises.
3. Route explicit and automatically generated `arithmetic()` tactics through
   that planner, then check only the resulting evidence.
4. Make expansion, printing, profiling, and audit retain and report the
   certificate consistently.
5. Add the deep-term and multi-size regressions, delete the old decision
   procedure and depth limit, update tactic documentation, and run the complete
   repository gate.

