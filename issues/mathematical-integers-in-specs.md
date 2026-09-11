# Offer mathematical `Integer` values on the specification side

**Current status:** dated checkpoints below are historical. The final
`Current integration review (2026-09-11)` section is authoritative for the
reviewed implementation checkpoint, its unfinished summation work, and the
scope gate before any new feature work.

Found by the 2026-09-01 kernel audit at cb034b21.

The standard library now offers an ordinary ADT `Nat`, recursive `nat_add`,
and Nat-valued `list_length`, with checked induction laws. This supports exact
structural sizes without machine overflow. It does not provide signed mathematical
integers, arithmetic automation, or checked conversions to/from C integers;
the requirements below remain open.

The original audit description predates wider integer support. The historically
named `Bitvector32Term` now also represents 64-bit terms. Signed arithmetic
already has overflow obligations, including in specification evaluation and
`arithmetic()`; unsigned machine arithmetic has modular semantics. The gap is
not a blanket absence of overflow checking. It is the absence of a separate
signed mathematical domain in which a specification can express an exact sum
independently of whether a particular C implementation can compute it safely.

Functional-correctness statements need a mathematical integer sort with explicit,
checked connections to machine integers. An exact sum must remain meaningful
when a C accumulator would overflow; the failure belongs to the C operation's
definedness obligation.

## Violated invariant

A specification should be able to state exact arithmetic facts, with the
relationship between machine values and their mathematical counterparts made
explicit and checkable.

## Agreed design (2026-09-10)

These are user-approved language decisions, not alternatives for implementers
to reconsider implicitly. Internal representation and certificate layout remain
implementation choices within this contract.

### Name and standard-library role

- The public type is `Integer`, with no `Int` alias. Existing `int` continues
  to mean the C `int32` type. Capitalization alone must not distinguish the
  two arithmetic domains.
- `Integer` denotes signed, unbounded mathematical integers. It has no C
  storage representation, ABI, machine width, or implicit runtime allocation.
- Present it as a standard-library type alongside `Nat`, with ordinary named
  lemmas and ordinary specification-type use sites. The kernel may support
  its terms and arithmetic directly; it need not be implemented as an ADT.
  The exact library declaration mechanism is an implementation choice.
- Keep `Nat` as the existing nonnegative mathematical datatype. Do not rename
  it or silently change its representation as part of this work.

### Explicit conversions and literals

- `to_integer(x)` accepts each supported signed or unsigned machine-integer
  type and preserves its numeric value. For example, signed `-1` maps to
  mathematical `-1`, while unsigned `4294967295u32` maps to mathematical
  `4294967295`. Equal bit patterns are not equal signed/unsigned values.
- Conversion of an already valid machine value to `Integer` is total.
  Evaluating the argument retains its existing obligations: converting the
  result of a C addition does not erase that addition's overflow obligation.
- Conversion back uses destination-specific names, such as `to_int32(z)`
  and `to_uint64(z)`. It generates a proof obligation that `z` is within
  that type's exact representable range. There is no implicit truncation,
  wrapping, saturation, or unchecked conversion.
- Machine values and `Integer` do not mix through implicit numeric coercion.
  Numeric literals may take their type from context, so `z + 1` is natural
  when `z: Integer`. Literals in this domain are not restricted to an
  implementation machine width. Existing machine-literal behavior remains
  compatible.
- `to_integer(a + b)` and `to_integer(a) + to_integer(b)` are different
  expressions. Relating them for signed machine addition requires evidence
  of no overflow; relating them for unsigned addition requires accounting for
  modular arithmetic. No unconditional rewrite may conflate them.

### Operators and definedness

- Initial operations are integer literals, unary negation, addition,
  subtraction, multiplication, equality, disequality, and order comparisons.
  Exact addition, subtraction, multiplication, and negation do not overflow.
- Keep bitwise operations on machine types; mathematical-integer bitwise
  operators are not part of this feature.
- Division and remainder use Euclidean semantics: for nonzero divisor `d`,
  `a == (a / d) * d + a % d` and `0 <= a % d < abs(d)`. Thus `-7 / 3 == -3`
  and `-7 % 3 == 2`. This deliberately differs from C truncation toward zero.
  A zero divisor creates a definedness obligation. These operators may land
  after the initial arithmetic stage, but their eventual meaning is settled.
- A checked conversion or division in a specification must not introduce an
  arbitrary assumption. Its definedness must be established in the relevant
  proof context before a successful theorem or execution certificate is
  published.

### Specification-type coverage

- Support `Integer` in specification bindings, universal and existential
  quantifiers, pure function parameters and results, theorem parameters,
  datatype fields/type arguments, and resource model fields.
- Reuse existing operators, binders, function syntax, and fold syntax. New
  mutable ghost-variable or C loop constructs are not required.
- Type fold indices independently from accumulators. In particular, an
  `int32` index may select C array elements while an `Integer` accumulator
  computes an exact sum. Mathematical-integer ranges are also supported.
- Preserve existing empty/reversed range behavior and capture-avoiding binder
  substitution. A fold's initial value and body must agree on accumulator
  type; contextual literal typing must not silently select machine arithmetic.
- Keep quantified proof rules sorted. Finite enumeration is a bounded proof
  technique, not an assumption that the `Integer` domain itself is finite.

### Relationship with `Nat`

- Provide explicit conversions in both directions. `Nat` to `Integer` is
  total; `Integer` to `Nat` requires a proof of nonnegativity. Exact spelling
  can follow the conversion naming scheme (`to_integer`, `to_nat`).
- Provide checked round-trip and arithmetic relationships rather than
  identifying the types by coercion. The existing structural `Nat` theorems
  remain useful independently of numeric automation.

### Proof automation and trust boundary

- Initially automate linear arithmetic: addition, subtraction, order, and
  multiplication by constants, together with explicit machine-conversion
  rules. General multiplication is a valid term without a promise of general
  nonlinear automation.
- Successful arithmetic automation must yield independently checkable,
  inspectable evidence that `click expand` can print and ordinary verification
  can recheck without invoking the planner. Coordinate this boundary with
  [arithmetic.md](arithmetic.md); do not enlarge the existing hidden kernel
  arithmetic decision procedure as the new feature's foundation.
- Supply explicit fold laws for empty ranges and a next-element step, plus
  the arithmetic evidence needed for bounded sums. Do not depend on array
  enumeration to verify a symbolic loop.
- Preserve existing C semantics, memory/snapshot and ownership rules, and
  the independent kernel certificate boundary. Treat the C regression source
  as fixed. No no-op branches, proof-only C locals, helper rerouting, or
  identifier changes are acceptable ways to make its proof succeed.
- Respect `docs/internals/verification-efficiency.md`: use local certificate
  checks, explicit premise references, bounded enumeration, and deterministic
  scaling regressions. Include numeric bit length in arithmetic work
  accounting. An enormous mathematical range must not trigger uncontrolled
  eager enumeration, and large constants must not silently truncate.

## Intended regressions

### Small semantic and certificate regressions

Before the loop example, cover exact values beyond both signed and unsigned
64-bit ranges; negative arithmetic; contextual literals; rejection of mixed
machine/mathematical operations; every supported machine conversion at and
outside its bounds; signedness; round trips; and rejection of an unconditional
machine-addition conversion identity. Include quantified variables, pure
functions, datatype/resource fields, and `Nat` relationships as their coverage
lands. When division/remainder land, test both signs of divisor and dividend
and reject zero-divisor proofs.

Arithmetic evidence needs tamper tests for premises, operators, coefficients,
terms, and range claims. Expansion, ordinary verification, profiling, and audit
must agree. Explicit proof checking must scale with the selected expression
and certificate, including numeric sizes, rather than unrelated proof state.

### Unchanged C summation loop

Mdtest over `int32 sum(int32 a[], int32 n) { int32 total; int32 i; total = 0;
i = 0; while (i < n) { total = total + a[i]; i = i + 1; } return total; }`.
Require `0 <= n and n <= 1000`, the necessary memory access authority, and
the bound `forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and
a[k] <= 1000 }` available at entry through a supported memory-reading
precondition or explicit contract fact. Keep that transport independent from
the integer feature; the old issue's memory-read issue link is obsolete.

The intended postcondition is
`to_integer(result) == (0..n).fold(0, |acc, k| acc + to_integer(a[k]))`,
with the fold accumulator typed `Integer`. The loop invariant relates
`to_integer(total)` to the corresponding prefix fold through `i`.

Also establish prefix bounds, either as a loop invariant or through an
explicit bounded-sum theorem. If `S(i)` denotes the mathematical prefix sum,
use `-1000 * to_integer(i) <= S(i)` and
`S(i) <= 1000 * to_integer(i)` along with `0 <= i and i <= n`.
The equality invariant alone does not prove that each intermediate C sum
fits. A small final sum can have overflowing intermediate prefixes.

A negative mdtest that drops the element bound must leave the exact sum
well-defined and fail on the overflow obligation at `total + a[i]`, rather
than assigning modular meaning to the invariant. Add a concrete neighboring
case with an overflowing prefix and a representable final mathematical sum
to guard against checking only the final result.

## Implementation review decisions (2026-09-10)

- Preserve symbolic expression sharing across specification abbreviations.
  A chain `a0 = x; a1 = a0 + a0; ...` has linear source size and must not
  materialize its exponentially expanded arithmetic tree. Constant folding
  alone does not meet this requirement. Use immutable shared Integer nodes
  with stable, shallow identities, and visit each reachable node once in
  appropriate traversals. This preserves ordinary source binding semantics.
- Shared-node identities must remain sound across threads and while any live
  term refers to them. Interning keys must contain shallow child identities;
  cache maintenance must not repeatedly hash an unrelated large numeral or
  retain dead expression graphs indefinitely. Renaming/substitution caches
  must account for lexical binder scope.
- Distinguish numeric literals that can take an expected type from expressions
  that establish an Integer type. Merely adding an unused Integer parameter
  must not change validation or machine arithmetic in another clause.
- Numeric work checks must consume the active verification budget before the
  operation. Recording a testing counter after arithmetic is insufficient.
  Keep the expression-visit budget separate from magnitude-dependent cost;
  do not simulate a weighted charge with a loop of unit checkpoints. Setup
  lowering runs before tactics start, so each numeric operation also checks
  the configured simple-operation allowance (the default when unconfigured).
  A constant-squaring alias chain must fail before the oversized multiplication.
- Structural substitution and generic rewriting preserve raw shared arithmetic
  nodes. They must not eagerly evaluate newly constant expressions: substituting
  `2` into a repeated-squaring DAG can otherwise allocate an enormous numeral
  from a tiny proof. Validate a shared replacement once, then charge its shallow
  root copy at each occurrence. Regressions cover both paths at depths
  8/16/32/64, including many occurrences of a growing shared replacement.
- Explicit arithmetic certificates permit zero premises for tautologies.
  Validate indices before allocating storage; a sparse enormous premise index
  must fail locally. Every supplied premise must be exactly available, and
  the kernel must validate every claimed node result independently.

The exact-value kernel foundation and checked pure Integer universal
specialization have passed the full gate and are integrated. The scalar source
stage adds theorem parameters, typed specification aliases, contextual literals,
pure theorem applications (including exact `using` guards and mixed C/Integer
parameters), and printable linear arithmetic evidence. Symbolic aliases retain sharing
through validation, lowering, rewriting, substitution, and arithmetic checking;
the depth-8/16/32/64 regression checks the complete simple-proof path. Alpha keys
serialize the shared graph with local child indices so equality and hashing
also avoid tree expansion. Certificate lowering borrows the mathematical
bindings without cloning unrelated C state for each evidence node.

This is a staged implementation, not completion of this issue. This paragraph
records the scalar boundary before the later checkpoints below; it is not a
current inventory of the implementation. The current landed boundary and the
remaining array, resource-pattern, existential, and summation work are recorded
in the 2026-09-11 status checkpoint at the end of this document.

## Quantifier review checkpoint (2026-09-10)

The reviewed theorem-application stage is integrated at `c34239af`. It includes
simultaneous argument binding (callee parameter names cannot change later caller
arguments), exact explicit-premise checks, rejection of missing or altered
guards and implicit C/Integer mixing, and expansion followed by re-verification.
The full gate passed on the current integration base: 2,135 unit/binary tests
and 14 integration gates.

The next source-quantifier stage remains isolated and is not part of the supported
language yet. Review established these additional implementation requirements:

- Introduction must freshen mathematical binders in the Integer carrier. An
  ambient fact about a same-numbered variable must never prove a universal claim.
  C and Integer source bindings must shadow each other in both directions.
- Reserve variable identities from the captured Integer arguments actually
  referenced by a proposition. A fixed allocator starting at `2_000_000` can
  capture an introduced or applied argument. Cache a maximum variable identity
  per shared Integer node so finding that bound does not traverse a shared DAG.
- An existential body's evaluation guards cannot be turned into an implication
  under the existential. That would allow an irrelevant witness with a false
  guard to prove the claim. The first lowering implementation must reject
  non-total or branching existential bodies unless it proves a sound treatment
  of guards and definedness for the same witness.
- A goal carries its complete persistent Integer binding environment. Initialize
  it once and update only the introduced name; do not merge or copy an entire
  binding overlay on every tactic.

### User-approved deferral of deep-quantifier scaling (2026-09-10)

The user explicitly chose to defer the quadratic work in repeated universal
introduction and continue the mathematical Integer feature. This is a narrow
exception to the repository's general scaling requirement for this known path;
it supersedes the earlier instruction to stop Integer work on this finding.

Each introduction currently validates, substitutes, and copies the remaining
boxed proposition body. With `n` nested binders and `n` explicit `intro()` steps,
this creates quadratic work. The reduced test at depths 8/16/32/64 measured
122/370/1250/4546 deterministic work units in the freshening helper, both with
empty assumptions and with an ambient quantified tautology using overlapping
binder identities. These are lower bounds on the complete proof path because
additional proof-state and Surface statement copying is excluded.

This was a synthetic stress test. We have not identified a realistic Integer
proof that becomes impractically slow because of deep quantifier nesting. Do not
make a general shared-proposition or deferred-substitution refactor a prerequisite
for shipping the otherwise working quantifier feature. Retain the reproduction
and revisit this cost when realistic proof workloads expose it.

The deferral does not relax proof correctness or existing work limits. Preserve
Integer carrier checks, capture-avoiding substitution, exact binder mappings in
expanded proofs, and rejection of invalid proofs. Do not bypass validation, raise
budgets, or change C programs. Other tooling failures and unrelated scaling
requirements remain subject to the repository policy.

A future fix should measure complete checked introduction at several depths,
including empty assumptions, ambient bound/free variable collisions, and source
expansion followed by independent verification. Sharing immutable proposition
bodies, retaining checked type/scope metadata, and avoiding repeated eager
renaming are likely parts of that fix. Simply skipping validation on a fresh
binder would be unsound; changing only the fresh-variable search is insufficient.
This refactor is deferred, not claimed complete, and is not an acceptance blocker
for the mathematical Integer feature under this user-approved exception.

## Machine conversion and certificate test checkpoint (2026-09-10)

The machine observation backend (`e5d6879b`) and source conversions (`b34a8cc7`)
are integrated after full `scripts/check.sh` gates. `to_integer` accepts all seven
supported machine integer types and preserves signedness. Constant reverse
conversions check each destination's exact bounds. Source regressions cover both
endpoints and both adjacent invalid values for every destination, wrong carriers,
arity, implicit mixing, and a reflexive claim whose C argument overflows.
Symbolic reverse conversions and the checked arithmetic laws relating C operations
to Integer operations remain under implementation; this checkpoint does not claim
them complete.

Machine observations are distinct typed opaque atoms for affine checking. Rewriting,
substitution, variable collection, interface identity, and parameter-read analysis
must descend into the observed C expression. Regressions cover pointer offsets,
C-variable substitution, signed/unsigned distinctions, and rejection of an
unconditional conversion-of-addition identity. Already evaluated machine values
enter the shared Integer DAG directly; alias chains retain bounded deterministic
work at depths 8/16/32/64. Conversion proof expansion rechecks independently.

External review identified insufficient shared-machine headroom in the exhaustive
binary certificate test. Commit `3052b88f` preserves the complete original case
matrix and independent counterexample oracle, partitioned by seven left-expression
families and two rules into 14 tests. The full gate measured 1.3–2.2 seconds per
partition, compared with roughly 22–32 seconds for the original test. The existing
60-second cutoff and all verifier budgets are unchanged.

## Pure quantifier checkpoint (2026-09-10)

Pure theorem proofs support source-side `Integer` universal introduction and
existential witnesses, including capture-avoiding shadowing, nested `have`, and
smart arithmetic proofs that expand and independently reverify. Mixed
machine/`Integer` carrier expressions remain rejected unless an explicit
conversion supplies the boundary. General existential elimination and deeper
mixed-carrier quantified reasoning remain later work; this checkpoint does not
claim those paths are implemented.

## Datatype and resource field checkpoint (2026-09-10)

Integer fields and generic arguments such as `Box<Integer>` are integrated in
`f7570a38`. Known-constructor matches extract correctly typed fields and shadow
outer bindings. The contemporaneous note that symbolic Integer-valued datatype
matches rejected is historical: the shared-body, carrier-aware match work is
covered by the 2026-09-11 integration checkpoint below and landed in
`7543105f`.

Resource schemas now accept Integer fields, which carry exact mathematical values
without adding C storage. Named instances preserve current and entry snapshots;
unfolding and folding check declared resource facts. Regressions cover large
values, updates distinct from `old(...)`, invalid machine-typed initializers,
negative initializers violating a nonnegative fact, and expansion/rechecking.
Resource initializer coverage includes Integer fields and must retain their
declared carrier and definedness obligations. Resource pattern bindings are a
separate checked surface: each bound field must keep its declared name, type,
and snapshot while the pattern is lowered and later rechecked.
An unchanged C memory read verifies against a field related to memory by
`to_integer(p[0]) == value`. Variable collection traverses observed machine
expressions inside deferred Integer arithmetic and algebraic field values.

## Signed addition bridge checkpoint (2026-09-10)

The standard library exposes `int32_add_to_integer` and
`int32_subtract_to_integer`: defined signed C operations agree exactly with
Integer addition/subtraction. `int32_add_defined_by_integer_bounds` establishes
C addition safety from the exact mathematical sum's lower and upper bounds.
These are explicit kernel arithmetic laws, checked against their precise library
declarations and applied through ordinary theorem certificates. No unconditional
conversion distribution rule or new tactic syntax is introduced.

Boundary-model tests evaluate the emitted laws independently, including modular
machine results and signed overflow. Source tests reject missing definedness or
either missing mathematical bound; accepted applications expand and reverify.
The unchanged C summation loop, general folds, and other machine-width operation
bridges remain to be completed.

## Pure Integer function checkpoint (2026-09-10)

Integer-to-Integer pure functions retain opaque canonical application nodes until
an explicit unfold. Linear arithmetic treats a result as an opaque Integer atom;
it does not assume the function's defining equation. Positive and negative source
regressions distinguish those behaviors and expanded proofs independently recheck.

Application argument storage is shared, node identities never repeat, and bounded
cleanup revisits live entries so their arguments can be released after they die.
Direct tests cover C and nested Integer argument substitution, cleanup lifetime,
and deterministic DAG rewriting at depths 8/16/32/64. The earlier caveat that
Nat and general argument types remained a separate call-lowering stage is
historical; scalar folds and ADT/Nat coverage are established by `77bd9f82`,
while the reviewed snapshot/affine support is landed in `7543105f`. Array-ref
acceptance and resource pattern bindings remain pending as recorded below.

## Implementation and integration sequence

1. Land this design record, then agree on the minimal shared kernel/surface
   interfaces before concurrent implementation of dependent pieces.
2. Add exact integer representation and local checked operations with direct
   boundary/soundness tests; thread the new sort through the logical term
   machinery without introducing a C runtime type.
3. Add surface typing, literals, explicit machine conversions, and scalar
   theorem/function regressions against the established kernel interface.
4. Add explicit arithmetic evidence and its expansion/printing support,
   coordinating the existing arithmetic-certificate work.
5. Complete datatype/resource fields and `Nat` relationships; generalize
   folds and quantified proofs and add their checked laws.
6. Verify the unchanged summation loop and its negative cases, complete
   documentation and deterministic scaling coverage, and run the full gate.

Delegate bounded pieces to Luna agents in separate task branches/worktrees.
Review contributions before integrating them. Every integrated commit must
be coherent and green under `scripts/check.sh`; dependent tasks start from
the reviewed interface commit. Check that the primary checkout is clean and
its base is current before integration. Do not merge partial implementations,
failed prototypes, or weakened tests merely to make parallel work fit.

## Acceptance criteria

- The approved `Integer` name, exact arithmetic semantics, contextual
  literals, explicit conversions, and checked definedness are implemented
  without changing existing machine arithmetic or C source semantics.
- `Integer` has the specification-type coverage described above, including
  `Nat` connections, typed folds, and sorted quantified proofs.
- The unchanged C summation loop proves exact functional correctness and
  intermediate overflow safety; negative regressions fail at the intended
  obligations without malformed or unverifiable certificates.
- Arithmetic planning produces explicit locally checked evidence; expansion,
  verification, profiling, and audit agree. Bounded failures are prompt and
  actionable, and deterministic scaling coverage includes large integers and
  unrelated-context sizes.
- Standard-library/user documentation describes the type and conversions,
  mathematical versus C arithmetic, and the supported automation fragment.
- `scripts/check.sh` passes before each integration and final completion.
- Division/remainder may follow initial arithmetic in a separate stage with
  the already agreed Euclidean semantics; do not claim their support before
  the corresponding implementation and regressions land.

## Mandatory conversion obligations checkpoint (2026-09-10)

Symbolic reverse conversions retain their destination carrier and require both
exact Integer bounds for all seven machine types. A reflexive comparison is not
a way to bypass those requirements; missing either bound rejects even when the
converted terms on both sides are identical.

Review found a related forward-conversion gap: the successful evaluation path of
`to_integer(x + 1)` carried non-overflow as a path assumption. Consequently a
reflexive goal could verify without establishing that its C argument was defined.
Forward conversions now retain the complete argument domain as a mandatory
verification condition, including intermediate operations and conditional paths.
Proof lowering and expression capture preserve typed obligations until checking
against independently established facts. Combining expression paths must preserve
mandatory status and diagnostic context, never turn the condition into an
assumption available to subsequent evaluation.

Regressions cover unbounded reflexive claims, established definedness, nested and
cancelled arithmetic, both operand positions, aliases, conditional branches,
owned memory reads, exact reverse bounds, and expansion followed by verification.
The checked C arithmetic bridge still requires definedness explicitly. This
checkpoint does not complete the remaining functions, quantified proofs, Nat
connections, folds, or unchanged C summation-loop acceptance work.

Datatype reflexivity must distinguish state independence from absence of
evaluation obligations. An Integer field can contain a checked conversion even
when it reads no memory. The shortcut now recursively checks that it cannot skip
an obligation; wrapped and nested-wrapped conversions retain the same required
argument definedness as an unwrapped expression. Guarded positive proofs expand
and reverify, while the identical reflexive goals without definedness reject.

## Machine round-trip laws checkpoint (2026-09-10)

Each machine destination has an explicit `integer_to_<type>_round_trip` standard
library theorem. Given both exact representable bounds, it proves
`to_integer(to_<type>(z)) == z`. The kernel constructs the guarded law, and
library loading checks its exact declaration before ordinary theorem application
can use it. Source tests remove each bound in turn and independently reverify
expanded applications. Boundary models check the emitted propositions against
modular conversion and signed interpretation for all seven widths/carriers,
including values outside their ranges and beyond 64 bits.

## Nat conversion law review (2026-09-10)

The builtin `to_integer(Nat)` observation and checked `to_nat(Integer)` conversion
have reserved meanings independent of ordinary function bodies. Their kernel
laws validate the complete Zero/Succ Nat schema, exact operation names and
argument counts, conclusion, and nonnegative guard. They must never infer the
meaning of a user function merely because it is named `nat_to_integer`.

The laws cover Zero, successor observation, nonnegative observations, both
round trips, and conversion of zero. Reverse conversion remains symbolic even
for very large Integers. The mandatory nonnegative obligation can be discharged
intrinsically for a checked Nat observation; other inputs require established
facts. Nested constructors cannot hide this obligation. Source applications
expand and reverify; independent structural/BigInt models check the kernel laws
and reject altered formulas, missing guards, and malformed Nat schemas.

`nat_integer_add` now derives the addition relationship by ordinary Nat induction
and explicit Integer certificates. Certificate lowering accepts checked C/Nat
observations and pure Integer function applications as atoms. It retains the
scalar path and selects only referenced bindings for mixed atoms, preserving
mandatory definedness checks. A deterministic 8/16/32/64 regression grows both
unrelated C parameters and explicit certificate nodes together.

## Quantified mixed atoms checkpoint (2026-09-10)

Integer quantifier substitution traverses opaque function arguments and checked
machine-conversion payloads, including reverse conversions. It keeps variable
carriers distinct, freshens nested Integer binders, preserves arithmetic DAG
sharing, and does not evaluate newly constant arithmetic during substitution.
Ordinary C atomic comparisons may accompany Integer clauses. Integer witnesses
use checked expression capture and retain conversion definedness obligations.
Expanded function applications promote introduced Integer names inside arguments;
their generated certificates independently reverify.

The older rejection of internal match/fold scopes is superseded by the scoped
match/fold work landed in `7543105f`. At this earlier checkpoint, array
snapshots and their source-level obligations were still pending, as were nested
quantifiers of other sorts; the current staged status is recorded below.

## Memory incident during isolated match review (2026-09-10)

The host kernel recorded an out-of-memory kill of a Click unit-test process at
19:34 local time (about 11.3 GiB resident, 30.5 GiB virtual). An isolated nested
match regression duplicated each previous expression into two owned arm bodies,
causing exponential construction and copying. A capped reproduction reached
roughly 442 MiB before its five-second CPU limit stopped it.

Match arms now hold shared Integer bodies; keys, substitution, variable collection,
and diagnostics preserve that sharing. The same depth-8/16/32/64 regression
finishes in about 0.02 seconds at 19 MiB. This was the experimental fix that was
subsequently reviewed and landed with the current snapshot/affine checkpoint;
the old statement that it was not integrated is retained only as incident
history.

For the remainder of this implementation, the coordinator runs only one build
or verification job at a time, with one build job and one test worker. Unreviewed
scaling experiments run under a hard memory and CPU limit before any full gate.
The interrupted combined gate is not a passing result and must be rerun.

## Integration checkpoint (2026-09-11)

The main scalar/match checkpoint is `77bd9f82`; it established the scalar-fold,
ADT, and Nat coverage. The reviewed snapshot and affine continuation are landed
in `7543105f`. Root verified that checkpoint's full gate at 2,356 unit and
binary tests plus 14 fixtures. It extends the earlier coverage with exact
snapshot identity and affine-fold checks. This section supersedes the earlier
experimental-branch status above.

The reviewed match design keeps arm bodies as shared Integer terms, performs
capture analysis by carrier, treats memory snapshots as opaque, and stops
actual traversal on exhaustion while measuring attempted visits independently.
Contextual numeral typing is retained: numerals in an Integer match context
are mathematical Integers, while machine values remain explicitly typed.
Fold coverage includes guarded empty-range and append/next-element laws.
Fold terms are supported as opaque atoms in linear certificates. Alpha matching
uses exact snapshot-aware identities, so alpha-equivalent loads from one retained
snapshot can match while unrelated snapshots remain distinct.

At this checkpoint, the remaining acceptance work was scoped definedness for
array-ref bodies, guarded existential post-witness proofs, resource pattern
bindings, and acceptance of the unchanged summation loop. The order bridge is
landed in `c5c29afa`; `scripts/check.sh` passed with 2,359 unit and binary tests
plus 14 fixtures. The approved Euclidean division/remainder deferral is
unchanged. Quadratic work in deeply nested universal-quantifier introduction
also remains deferred; quantifier support itself is implemented. The staged
status of those slices is recorded below.

## Current integration review (2026-09-11)

The reviewed implementation checkpoint retains the previously unit-green
scalar, datatype, quantifier, fold-law, resource-pattern, indexed-witness,
snapshot-alpha, order-bridge, and bounded affine-certificate work. The mixed
match/fold source cases, shared replacement universal-quantifier regression,
and binder-collector memo fix are included in the reviewed work landed in
`7543105f`. The checkpoint intentionally excludes unfinished unchanged-C
summation acceptance while retaining the negative fixtures for missing element
bounds and intermediate machine overflow:
`integer_sum_range_fold_missing_bounds.md` and
`integer_sum_range_fold_intermediate_overflow.md`.

The scalar, match, snapshot, and affine baseline for this checkpoint passed its
full gate with 2,435 unit and binary tests plus 14 fixtures. The implementation
checkpoint was merged and pushed as `0c71c2de`. On the latest integration base,
`scripts/check.sh` passes with 2,446 unit and binary tests plus 14 fixture
gates.

The focused slices retained in this checkpoint are:

- Array-ref fold bodies preserve opaque snapshots and scoped definedness. The
  focused source cases pass ordinary verification, expansion, and independent
  re-verification.
- Guarded and fixed-witness Integer existentials pass their positive cases,
  missing-definedness negative, expansion, and re-verification, including the
  indexed memory-bearing witness.
- Resource pattern bindings have 13 focused kernel/resource checks and the
  corresponding source cases passing. Integer resource initializers and
  pattern bindings retain declared field carriers, names, snapshots, and
  definedness through expansion.
- Fold terms are exact snapshot-aware opaque affine atoms. The bounded planner
  accepts only checked selected premises, explicit constant scaling, and the
  reviewed one- and two-premise combinations; atom identity is recomputed by
  the kernel and is never taken from a raw term ID or fingerprint alone.

The checkpoint intentionally omits the failing positive
`integer_sum_range_fold.md` fixture, its unvalidated expansion regression, and
the recent loop-closure patch with its two tests. Those files are not evidence
that unchanged-C summation acceptance is complete. The remaining work is to
reduce the smallest failing generated bundle to a bounded leaf diagnostic,
repair that checked closure, and then verify the positive source ordinarily,
expand it, and independently re-verify the expanded proof.

The diagnostic run established all five individual invariant `have` steps under
ordinary checking, but not the combined generated-bundle closure or expansion.
The first diagnostic confirmed an implementation presentation gap: the source
synthesis path could not reconstruct a Surface presentation for the generated
mathematical-Integer comparison goals in the loop-close bundle. Integer
comparisons themselves remain expressible in the language. A subsequent narrow
patch removed the gate failure, but the same generated bundle still failed. The
preserved older reproduction remains in
`/tmp/click-integer-sum-integration`; the standalone source recheck is
`/tmp/click-integer-sum-reproduction/integer_sum_range_fold.click`. Running
that source with the landed binary now fails promptly in `sum.contract` source
tactic 44 with `closure body did not prove every invariant obligation` (0.29
seconds), so this is a proof-closure failure rather than a timeout. The exact
underlying leaf is still unknown. The next step is a bounded reduction of the
smallest failing bundle with explicit leaf facts and source provenance, rather
than a broad Surface implementation.

The proposed next regression should isolate the goal shape
`L and (L -> (L -> E))`, where `L` is the scoped loadability universal and `E`
is the checked Integer fold equality. Supply `L` and `E` as explicit premises;
the leading conjunct exercises `Both`, while the nested implications exercise
`Intro`. Compare the checked `Both`, `Intro`, and `Assumption` paths with the
smart closer when the source presentation is absent, and reject a proof that
lacks `E`. Then
inspect the actual remaining bundle leaf. This is a bounded diagnostic and
regression proposal, not an implemented or confirmed semantic extension.

The process diagnosis is that merge was made dependent on whole-sum acceptance
before the smallest failing bundle had been isolated, reduction happened too
late, and intermediate integration checkpoints were not recorded. Scope and
process review for this checkpoint is complete. No new feature work should
begin until this closure is reduced and reviewed against the latest base; the
remaining leaf is still unknown.

This checkpoint preserves the approved design: existing C remains unchanged;
fold atoms use exact snapshot-aware identities rather than raw IDs or
fingerprints; certificates use explicit checked premises and bounded work; and
range enumeration, unchecked assumptions, whole-state scans, and general
unbounded affine search remain out of scope. The user-approved deferral of
deeply nested universal-quantifier scaling remains in force, as does the
Euclidean division/remainder deferral.
