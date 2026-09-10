# Offer mathematical `Integer` values on the specification side

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
