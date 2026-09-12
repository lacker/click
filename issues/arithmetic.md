# Make `arithmetic` smart and expand it to `arithmetic_certificate`

## Priority and relationship

This is P1. It is the last kernel decision procedure hidden behind a simple
tactic after the 2026-09 kernel-search cleanup (see the kernel authority
boundary in [proof-objects.md](../docs/internals/proof-objects.md) and
[simplify-step.md](simplify-step.md) for the other remaining route). It is its
own issue because its certificate vocabulary, arithmetic rules, diagnostics,
and expansion design form one coherent unit. The boundary is not closed while
`arithmetic()` reconstructs a proof internally or while
`ARITHMETIC_INTERVAL_DEPTH` can change whether a supported proof succeeds.

Mathematical `Integer` arithmetic already has the intended planner/checker
split and a source-printable `integer_certificate`. This issue incorporates
that implementation into the unified public arithmetic design rather than
creating a parallel family of `int32_certificate`, `int64_certificate`, and
similar tactics.

## Violated invariant

The kernel checks an explicitly chosen derivation; it does not reconstruct a
nontrivial derivation hidden behind one apparently simple proof step. A surface
smart tactic may inspect the current goal and its permitted premises, choose
arithmetic bounds and rules, and emit a certificate. Kernel work should then be
a linear sequence of local checks whose cost and completeness are determined
by that certificate.

`arithmetic()` is currently classified as a simple tactic, but its kernel
operation is a small arithmetic decision procedure. The surface step names the
premises and goal, not the derivation between them. The kernel normalizes
expressions, combines inequalities, reconstructs intervals for nonlinear and
bitwise terms, checks signed-overflow side conditions, and decides whether the
goal follows. That reasoning is deterministic and restricted to explicit
inputs, so it is not ambient proof search, but it hides substantially more
planning than a simple tactic may perform.

The intended design is:

```text
arithmetic()                         smart user request
    -> surface arithmetic planner   chooses typed rules and premises
    -> arithmetic_certificate       records the complete derivation
    -> kernel certificate checker   checks only local referenced rules
```

Planning belongs in the surface layer. The kernel retains only explicit,
locally checkable arithmetic and conversion rules.

## Agreed public language design

`arithmetic()` is the ordinary user-facing tactic for supported arithmetic.
It chooses the appropriate typed arithmetic reasoning from the goal and emits
an explicit proof:

```click
arithmetic();
arithmetic() using {
    0 <= x;
    x <= 10;
}
```

The no-premise form remains context-free. The `using` block remains the exact
premise universe: every listed proposition must be available, and unlisted
ambient facts are invisible. `simp()` may select relevant facts and delegate an
arithmetic subgoal to the same planner, but neither ordinary verification nor
expanded verification may treat a generated certificate as permission to scan
ambient facts.

`click expand` replaces a successful `arithmetic()` with one public,
source-printable low-level form:

```click
arithmetic_certificate {
    // Typed premise, arithmetic, conversion, and conclusion nodes.
}
```

`arithmetic_certificate` is technically a simple tactic because it appears in
a proof script and applies one explicit checked derivation. It is primarily an
expansion and audit format, not the interface ordinary proof authors are
expected to choose. It performs no planning, premise selection, alternate
derivation search, or recursive proof attempts.

Do not add one public certificate tactic per numeric width. In particular, do
not introduce `int32_certificate`, `int64_certificate`, `uint32_certificate`,
or `nat_certificate`. The certificate contains typed rule families instead.
Each local arithmetic node operates in one checked carrier, while explicit
conversion nodes connect carriers when one proof involves more than one sort.
For example, mixed `int32`/`int64` arithmetic is represented as a checked
`int32` fact, an explicit widening step, and `int64` arithmetic—not as an
untyped mixed addition rule.

The current `integer_certificate` implementation becomes the mathematical
`Integer` rule family under `arithmetic_certificate`. New expansion emits only
`arithmetic_certificate`. The implementation may temporarily accept
`integer_certificate` as a compatibility spelling if needed for migration, but
documentation and generated proofs must present one arithmetic-certificate
model. Internal typed certificate structs and checkers may remain separate;
unifying the public form does not require one monolithic kernel checker.

`Nat` remains an ordinary recursive algebraic datatype. Nat proofs continue to
use constructor reasoning, unfolding, induction, named theorems, and explicit
conversion to `Integer` when affine arithmetic is needed. This issue does not
add a native Nat arithmetic certificate theory.

## Supported domains and composition

The public `arithmetic()` tactic and the enclosing certificate format are not
restricted to one numeric sort per complete proof. The initial migration must
support the arithmetic domains already routed through current automation:

- mathematical `Integer` affine reasoning, reusing the existing checked
  certificate and bounded planner;
- signed `int32` affine and interval reasoning, including C definedness; and
- the pointer-alignment, pointer-translation, and finite-float-reflexivity
  cases currently represented by `ArithmeticUsing`.

Each checked node nevertheless has one precise rule and result type. A
multi-sort derivation composes homogeneous local arithmetic with explicit
bridges. Machine widening, narrowing, signedness changes, and conversion to or
from mathematical `Integer` must retain their existing checked semantics.
Certificate checking must never identify equal bit patterns across signed and
unsigned carriers, erase a narrowing range obligation, or turn a machine
operation into exact mathematical arithmetic without its definedness evidence.

The exact serialization may use one flat heterogeneous node vector or typed
subcertificates connected by explicit bridge nodes. In either representation,
the printed certificate must retain every type and conversion needed to prevent
its meaning from changing under a different surrounding typing context.

Adding new arithmetic capabilities is not required merely to make the format
extensible. The initial machine implementation may preserve the current
`int32` fragment while making width and signedness explicit enough that future
`int64` or unsigned rules do not require new top-level certificate tactics.

Pointer translation, pointer alignment, and finite-float reflexivity are not
machine-integer algebra. They may either receive clearly typed local rule nodes
inside `arithmetic_certificate` or expand to other existing or new public
simple rules. They must not remain hidden behind the removed
`ArithmeticUsing` certificate leaf, and they must not force pointer provenance
or IEEE semantics into the generic integer rule family.

## Current behavior

`ProofTactic::ArithmeticUsing` and `ProofStep::ArithmeticUsing` are currently
classified as `TacticClass::Simple(SimpleTactic::Arithmetic)`. Applying the
step lowers the listed propositions, checks that each is exactly available,
and calls `KernelProof::apply_arithmetic`.

That operation first tries finite-float reflexivity and pointer alignment. Its
remaining checker, `check_signed_affine_arithmetic` in
`src/kernel/proof/fact_reasoning.rs`, also tries pointer translation before
performing signed arithmetic. The signed path currently performs all of the
following work without an explicit derivation payload:

- recognizes and normalizes signed affine equalities, disequalities, and
  inequalities;
- establishes signed-`int32` definedness for affine goal expressions;
- accepts an identical normalized inequality or sums all selected inequalities
  with coefficient one, with explicit premise repetition representing a larger
  positive coefficient;
- extracts lower and upper bounds for canonical atomic terms;
- recursively propagates conservative intervals through supported products,
  constant remainder, constant left and arithmetic-right shifts, masked
  bitwise-and expressions, and the sign-bit flip used by unsigned comparisons;
- checks every relevant intermediate signed operation for overflow or another
  C undefined-behavior condition; and
- compares the resulting endpoint intervals, including a special
  shared-operand rule for arithmetic right shift.

The interval reconstruction is capped by
`ARITHMETIC_INTERVAL_DEPTH = 32`. `signed_term_interval` silently returns no
interval beyond that depth, so otherwise supported proofs depend on an opaque
nesting limit. Merely replacing the recursion with an iterative walk would make
that hidden decision procedure complete over its input, but would invest in
machinery this issue intends to remove from the kernel. The limit should
disappear as part of the certificate migration.

The surface is already partly acting as a planner:
`src/surface/proof/surface_certificates.rs`,
`src/surface/proof/pure_theorems.rs`, and execution proof code call the kernel
arithmetic checker to test whether an `ArithmeticUsing` step will succeed.
This coupling must be reversed. Surface planning owns the arithmetic algorithm
and produces the evidence consumed by the kernel rather than calling the
authoritative checker as a planning oracle.

Mathematical `Integer` is already different: `simp()` can invoke the bounded
Integer affine planner and emit `integer_certificate`, whose kernel checker
validates explicit premise, scale, add, equality-bound, trivial, and conclusion
nodes. Preserve that checked implementation and its scaling properties while
moving it under the unified public spelling.

## Required capability correction

The function-contracts campaign found this signed linear goal:

```text
0 <= a
0 <= b
defined(a + b)
----------------
0 <= a + b
```

The current checker rejects `defined(a + b)` because its premise parser accepts
only signed affine comparisons and equalities. Inferring definedness from the
two lower bounds is impossible because they provide no upper bound. The
certificate vocabulary must therefore be able to cite an exact existing
`defined(expression)` proposition and connect it to the same typed expression
whose affine conclusion is being proved. This is a deliberate extension of the
current signed premise fragment; it uses the existing `defined` proposition and
does not add a new expression-language construct.

The campaign also found the bounded affine goal:

```text
0 <= n
n <= 100
--------
n + n <= 200
```

The current checker either accepts one normalized inequality directly or adds
every listed inequality with coefficient one. It therefore cannot use the
upper bound twice unless the user repeats it in the `using` block. That is an
artifact of treating the premise list as a partial derivation. A smart
`arithmetic()` planner should choose the nonnegative coefficient two and record
that choice in `arithmetic_certificate`; the normal user interface should not
require duplicated premises for elementary scaling.

A further regression concerns arithmetic over a resource field after a call.
An equality such as `c.revision == 1` is available, but a `have` of
`c.revision < 1000` may have no checkable surface form at that proof state, and
the current arithmetic route cannot turn the equality into the strict bound.
The new planner must support the equality-to-bound arithmetic derivation when
the exact field premise is source-expressible. If the premise itself cannot be
serialized at the relevant snapshot, repair that Surface provenance seam; do
not put an internal-only resource-field term into the arithmetic certificate.

A separate reported example combines mathematical `Integer` equalities across
two calls but lacks a surface spelling for the intermediate historical value.
The existing Integer affine certificate can perform the algebra once its
premises are expressible. Synthesizing or exposing that call snapshot is a
call-state provenance problem, not an arithmetic-certificate rule, and is not
an acceptance criterion for this issue.

## Certificate boundary

A certificate must name the chosen route so the kernel never rediscovers it.
A likely checked representation has four layers:

1. **Premise references.** Refer to positions in the exact surface-supplied
   premise list. If a cited proposition is a conjunction, extraction must be an
   explicit ordinary `extract` step or a certificate node carrying a checked
   conjunct path; the checker must not silently flatten it.
2. **Typed local derivation nodes.** Record affine normalization and
   combination, bottom-up interval and definedness rules, and any pointer,
   float, or conversion rules retained in the common envelope. Each node names
   only earlier nodes and the local payload needed to check its result.
3. **Explicit bridges.** Record widening, narrowing, signedness, Nat/Integer,
   and machine/Integer conversions when a supported proof crosses arithmetic
   domains. A bridge is a checked rule, never an implicit coercion.
4. **Conclusion.** Select the exact checked proposition that must equal the
   current goal.

A flat, topologically ordered representation is preferred. It permits
iterative linear checking, makes forward and invalid references easy to reject,
avoids Rust call-stack dependence, and permits sharing without a cache keyed by
deep structural term comparison. A tree is acceptable only if it demonstrably
avoids duplicated proof text, repeated deep-term work, and recursive checker
limits.

The mathematical `Integer` affine nodes already provide a useful base:
premise, scale, add, equality-to-bound, equality-from-bounds, trivial, and
conclusion. Generalize their surface enclosure without weakening their typed
kernel checks.

Signed machine arithmetic additionally needs locally checked evidence for:

- affine normalization and nonnegative combination of selected inequalities;
- atomic lower and upper bounds tied to exact premise evidence;
- constants and opaque typed atoms;
- addition, subtraction, and multiplication intervals;
- constant signed remainder, including zero and `INT_MIN / -1`-family
  undefined behavior;
- constant left and arithmetic-right shifts, including shift-count and signed
  left-shift requirements;
- constant masks and sign-bit flips;
- explicit `defined(expression)` evidence;
- equality, disequality, and signed-order conclusions; and
- the existing shared-operand arithmetic-right-shift rule.

All intermediate signed operations must remain proven defined, not merely the
final result. The bitwise-and rule must retain its current operand-definedness
check even when a constant mask determines the result interval. Unsupported
operators fail planning promptly rather than triggering broader search.

Affine certificate evidence must state which inequalities are combined and
with what nonnegative coefficients. The smart planner may choose coefficients;
repeating a premise in the user's `using` block is not the coefficient
language. Planning must be bounded and proportional to the exact supplied
premise universe rather than becoming an unbounded linear-programming search.
Internal normalization must not acquire an opaque fixed-width coefficient
limit; use checked magnitude-aware arithmetic and charge work by numeric bit
length where necessary.

Interval nodes should carry their claimed endpoints. The checker recomputes
each result from its referenced children and rule, which improves diagnostics
and ensures that tampering with a bound is rejected at the node that introduced
it. Nodes must encode expression structure by operator and child reference
rather than repeatedly embedding complete deep child expressions.

## Diagnostics, expansion, and profiling

Ordinary failures should be reported at `arithmetic()` in terms of the user's
goal: unsupported operation or conversion, missing exact premise, possible
overflow or other undefined behavior, planner budget exhaustion, or valid
premises that do not imply the conclusion. Users should not receive a raw dump
of internal interval state.

An explicitly written or expanded `arithmetic_certificate` should instead
identify the rejected node and reason: invalid premise or conjunct reference,
forward child reference, wrong type, changed operator, coefficient, endpoint,
conversion, definedness evidence, or conclusion.

Profiling presents one smart `arithmetic()` site plus the cost of the explicit
certificate it generated. Expanded verification reports only the simple local
certificate work. `click expand`, ordinary verification, profiling, and audit
must agree on the same retained derivation and must never rerun the planner to
validate an expanded certificate.

## Intended regressions

Add a proof whose supported signed-arithmetic expression is nested more than
32 levels deep. Its surface arithmetic planner should produce an explicit
certificate, and checking that certificate should succeed with deterministic
work proportional to the expression and certificate sizes.

Add a neighboring proof with an overflowing intermediate signed operation deep
in the expression. Planning must not produce a successful certificate, and a
hand-constructed or tampered certificate claiming that interval must be
rejected locally by the kernel.

Add the explicit-definedness example above, plus a negative neighbor in which
the `defined(a + b)` premise is absent or refers to a different expression.

Add `0 <= n`, `n <= 100` proving `n + n <= 200` without repeating the upper
bound, and tamper with the generated scale coefficient. Retain the
resource-field strict-bound regression, with a source-printable certificate
whose premise resolves to the exact checked field value and snapshot.

Retain positive and negative coverage for existing affine, bounded-product,
remainder, shift, mask, sign-bit-flip, pointer-translation, pointer-alignment,
and finite-float-reflexivity behavior. Expansion of a mathematical `Integer`
proof that currently emits `integer_certificate` must instead emit the unified
form and recheck without invoking either planner.

Tamper tests must independently change every security-relevant reference or
payload: premise and conjunct selection, term, carrier, width, signedness,
operator, endpoint, coefficient, child reference, conversion, definedness
evidence, and final comparison.

Add deterministic multi-size regressions for deep expressions, certificate
node count, coefficient magnitude, and unrelated ambient facts. Checking must
remain near-linear in the explicit expression and certificate sizes, up to the
repository's documented logarithmic indexing and magnitude-dependent numeric
work.

## Acceptance criteria

- `arithmetic()` and `arithmetic() using` are smart tactics whose successful
  planning yields an explicit checked derivation.
- `simp()` delegates supported arithmetic goals to the same planner rather
  than maintaining a second arithmetic proof path.
- `click expand` emits the public `arithmetic_certificate` form; it does not
  emit `ArithmeticUsing` or create width-specific certificate tactics.
- `arithmetic_certificate` is parser accepted, source printable, inspectable,
  serializable with proof provenance, and independently checkable without
  invoking arithmetic planning.
- The existing mathematical `Integer` certificate implementation and planner
  are available through the unified public form. New generated proofs and
  documentation do not present `integer_certificate` as a separate arithmetic
  interface.
- Individual arithmetic nodes have one checked carrier. Every multi-sort proof
  uses explicit typed conversion nodes or separately checked bridge steps.
- The initial certificate representation can accommodate future machine widths
  and signedness without adding `int32_certificate`, `int64_certificate`,
  `uint32_certificate`, or similar top-level forms.
- The kernel checker uses only the goal, explicitly referenced premises, and
  certificate nodes. It performs no ambient fact selection, recursive proof
  attempts, or alternate derivation search.
- `check_signed_affine_arithmetic`, `signed_term_interval`, and
  `ARITHMETIC_INTERVAL_DEPTH` are deleted from the kernel, or reduced to
  clearly local certificate-rule helpers with no whole-goal planning role.
- Exact `defined(expression)` evidence can justify the same machine expression
  in an arithmetic conclusion, and a mismatched or missing definedness premise
  is rejected.
- The smart planner can choose explicit nonnegative affine coefficients, so
  `0 <= n` and `n <= 100` prove `n + n <= 200` without repeated user premises;
  the checker validates rather than rediscovers those coefficients.
- Arithmetic over a source-expressible resource field can use an exact equality
  to prove a constant strict bound, and its expanded certificate preserves the
  checked field and snapshot identity.
- Existing affine, bounded-product, remainder, shift, mask, sign-bit-flip,
  equality, signed-overflow, pointer, and float acceptance/rejection behavior
  remains covered or is migrated to another explicit public simple rule.
- A certificate with a changed premise, conjunct path, term, carrier, width,
  signedness, operator, endpoint, coefficient, child reference, conversion,
  definedness claim, or final comparison is rejected locally.
- Deep supported expressions no longer fail at an opaque nesting depth, and
  checking is iterative wherever certificate depth could exhaust the Rust
  stack.
- Multi-size deterministic regressions demonstrate near-linear checker work in
  explicit expression and certificate sizes. Unrelated ambient facts do not
  change that curve.
- `click expand`, ordinary verification, profiling, and audit agree on the
  expanded arithmetic proof and successfully recheck it without planning.
- User documentation describes `arithmetic` as the normal smart interface,
  `arithmetic_certificate` as its low-level expansion, the supported arithmetic
  fragments, exact-premise behavior, explicit conversions, and failure
  diagnostics.

## Non-goals

- A complete solver for nonlinear arithmetic or arbitrary quantified numeric
  theories.
- Adding new machine widths, unsigned arithmetic theories, division, logical
  shifts, conditionals, or additional bitwise automation merely because the
  certificate format can represent future typed families.
- Searching the ambient context from `arithmetic() using` or from
  `arithmetic_certificate`.
- Replacing arithmetic reasoning with an SMT solver inside the kernel.
- Weakening signed-overflow, conversion-range, pointer-provenance, IEEE, or
  other C definedness checks.
- Adding native `Nat` arithmetic primitives or a `nat_certificate`.
- Solving the missing surface spelling for historical values across calls.
- Preserving compatibility for low-level internal kernel APIs; Click currently
  has no such compatibility commitment.

## Suggested implementation order

1. Specify the common Surface `arithmetic_certificate` envelope, typed node
   identity, and composition boundary. Route the existing mathematical
   `Integer` certificate through it and make expansion round-trip before
   changing signed arithmetic.
2. Specify signed-machine affine, interval, explicit-definedness, and
   conclusion nodes with direct kernel unit tests, including malformed and
   tampered certificates.
3. Move signed affine and interval planning into the surface layer and have it
   produce the certificate from exactly the listed premises. Preserve current
   behavior before broadening planner heuristics.
4. Reclassify explicit and automatically generated `arithmetic()` tactics as
   smart, and route `simp()` arithmetic through the shared planner.
5. Migrate pointer translation, pointer alignment, and finite-float reflexivity
   to explicit checked nodes or other public simple rules, then delete the old
   `ArithmeticUsing` leaf and whole-goal kernel decision procedure.
6. Complete printing, parsing, provenance, profiling, audit, diagnostics,
   deep-term and multi-size regressions, compatibility cleanup, and user
   documentation; then run the complete repository gate.
