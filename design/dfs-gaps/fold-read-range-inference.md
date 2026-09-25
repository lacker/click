# Design: checked read ranges for fold applications

Status: delivery steps 1 and 2 landed; steps 3 and 4 are not started and
not authorized. `src/kernel/fold_read_summary.rs` holds the kernel-checked,
session-scoped read summary (step 1) and the explicit application-framing
rule that `transport(P, Q) using { ... }` reaches (step 2). The rule walks
the recorded memory history between the two array snapshots per query and
records nothing, so it did not need the open range-epoch representation
below; automatic reuse (step 3) still does. Kernel pointer offsets are exact
sums of sign-extended scaled `int32` terms, so the framing rule needs no
representable-extent bound: it reads the written offset exactly and asks one
exact order fact (`end <= j` or `j < start`), or a stated separation with
exact membership facts. The rule is not consulted inside a smart search
scope or closure, so `simp`'s snapshot transport closure does not reuse it;
the existing `mdtests/array_fact_does_not_survive_*.md` fixtures pin that.
Regressions: the kernel tests in
`src/kernel/fold_read_summary/tests.rs` (every unsupported read pattern,
byte-width boundary overlap, aliasing, lifetime and call edges, session
poisoning, and deterministic scaling over body size, application count,
unrelated facts, interval length, and store sequences),
`fold_read_summaries_are_checked_from_the_lowered_declarations` in
`src/surface/tests.rs`,
`explicit_fold_read_transport_along_a_store_sequence_is_near_linear` in
`src/surface/tests/scaling_tests.rs`, and the `mdtests/fold_read_transport_*.md`
fixtures plus `mdtests/sweep_prefix_survives_its_endpoint_store_by_transport.md`.
This design does not approve a general effect language.

## Decision and surface behavior

No new source syntax is needed for the first implementation. Infer a checked
read summary from an existing function definition, and use it to frame that
function's applications across unrelated writes. Keep the function's value
semantics, explicit `defined(...)` claims, and C access checks unchanged.

The motivating definition already supplies the relevant information:

```click
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| {
        acc + to_integer(if v[k] == 0 { 1 } else { 0 })
    })
}
```

For fixed scalar arguments, this application depends on the logical values
of `v[k]` for `lo <= k < hi`. A store to `v[hi]` can preserve its value;
a store to `v[lo]`, when `lo < hi`, cannot generally do so.

In `mdtests/sweep_maintains_a_zero_unmarked_count.md`, the intended benefit is
to preserve `unmarked(visited, 0, i) == 0` across `visited[i] = 1` without the
handwritten `unmarked_frame` lemma and quantified per-cell transport. The
subsequent increment changes the scalar argument `i`: proving the enlarged
prefix still needs the fold's append law. The DFS marking store is inside its
counted range, so its point-update and decrease proofs remain necessary.

A `reads v[lo..hi]` annotation would introduce another assertion to validate
without adding information for this case. Do not add one now. A future API
for abstract functions without bodies would be a separate design decision.

## Semantic authority

Inference establishes a sufficient dependency bound, not permission to read
memory. It is proof-relevant information used by the kernel, although users
need not write it. Treating it as an unchecked optimization would be unsound.

The rule to justify is extensionality. Fix the function definition, pointer
arguments, scalar arguments, and other value arguments. If each pair of array
snapshots agrees on every typed logical read in the inferred support, the two
applications have the same value. For this first case, finite fold induction
establishes the rule: the initial accumulators agree, and each iteration sees
the same accumulator, index, and array cell, hence produces the same result.
Both sides use the same range. An empty fold returns its initial value.

There are two independent checks:

1. Definition checking proves that the proposed support includes every read
   that can affect the fold's result.
2. Framing proves that the selected program effect preserves those reads in
   the selected snapshots.

Neither check can substitute for the other. An exact syntactic index match
alone does not establish byte disjointness. Nor can a separation fact justify
an incomplete dependency summary.

Logical reads remain total. Do not insert viewability or initialization guards
when lowering an application or a proposition about it. Any arithmetic or
footprint side conditions belong to the framing proof, not to the function's
logical denotation. A logical value equality must never supply C read
permission, initialization, or allocation liveness.

## First supported subset

Start with the `Integer`-valued, `int32`-indexed top-level range fold above:

- One `int32[]` parameter is read. The endpoints are `int32` scalar parameters
  or literals. The initial accumulator is a memory-independent Integer term.
- Every array read in the fold body is exactly that parameter at the bound
  fold index. Match binder identity, not its spelling. Multiple occurrences
  of the same read are allowed.
- The body may use the accumulator, index, scalar parameters, literals,
  total Integer arithmetic, comparisons, conditionals, and the total
  conversions needed by `unmarked`. Inspect conditions and both arms.
- Recognize an explicit whitelist of lowered expression constructors. Any
  unhandled constructor, nested fold, recursive call, opaque helper call,
  address escape, different array access, or read in an endpoint or initial
  accumulator declines inference for the entire definition.

For example, `v[k + 1]`, `v[v[k]]`, a branch that reads `v[hi]`, or passing `v`
to an opaque helper must retain the existing conservative dependency. Do not
silently summarize the recognized portion and omit the rest. An unsupported
function still verifies as it does today; only the framing improvement is
unavailable. Supporting multiple arrays, helper-summary composition, offsets,
nested folds, and recursion can follow separate evidence from real proofs.

An actual scalar argument may itself be a historical memory read. It is an
already evaluated value at this application, not an instruction to reload the
endpoint at each snapshot. Preserve its existing dependency and load identity.
If the later application supplies a different endpoint value or pointer,
range framing alone does not equate the applications.

## Representation and implementation boundaries

The current path explains why changing the resource tracker alone is not
sufficient:

| Location | Current role | Proposed responsibility |
| --- | --- | --- |
| `src/surface/lowering/annotations.rs` | Registers selected memory-independent definitions and lowers function arguments | Supply the supported fold definition in kernel vocabulary; preserve argument and binder identities |
| `src/kernel/pure_functions.rs` | Definition registry restricted to memory-independent functions | Add a separate checked fold-summary facility, without broadening the existing evaluator's authority |
| `src/kernel/spec.rs` | Lowers each array argument using a whole-block snapshot epoch | Assemble all application arguments before instantiating its checked support; retain whole-block fallback |
| `src/kernel/primitives/integer.rs` | Interns opaque Integer applications | Associate application support with checked definition identity and instantiated arguments |
| `src/kernel/resource_tracker/mod.rs` | Collects array-argument reads as whole blocks; supports cell/range resources | Query checked application support and preserve pointer/endpoint dependencies |
| `src/kernel/resource_tracker/step_effect.rs` | Checks whether an effect misses a resource | Check the instantiated byte range with the existing effect/lifetime boundary |

Do not add a smaller extent to a freely reusable `ArrayRef`. Its meaning must
remain the same when passed to another function, used by explicit unfolding,
or compared under another application. Support is associated with the
application and the checked definition that warrants it.

Use an immutable, session-scoped checked-summary handle. Its constructor is
kernel-owned and validates the lowered body; Surface cannot manufacture the
handle by asserting an interval. Include definition identity, parameter and
result sorts, fold binder identities, element width, and endpoint templates.
Scope caches to the verification session and distinguish changed definitions,
including imported definitions. A declaration without an available body gets
no inferred summary. The same definition must govern unfolding and framing;
there must not be two independently trusted versions of its body.

Derive the summary once per selected definition. Instantiate its small template
once per distinct application, with ordinary persistent sharing. A certificate
may refer to that checked handle only within the session that created it.
Expanded source continues to spell the original function application and
ordinary proof steps; a fresh verifier reconstructs and validates the summary
from the same definition.

## Range framing and snapshots

Instantiate a typed logical interval first, then justify its byte footprint.
For a nonempty `int32` interval, this means the base pointer plus the checked
index offset and a four-byte cell for each index. Use the kernel's actual
pointer-offset and range arithmetic. Do not assume unbounded integer address
arithmetic, nonnegative indices, nonwrapping multiplication, or disjointness
merely because two source expressions look different.

The first implementation may require the same explicit nonnegative endpoint
and representable-extent bounds already available in the sweep example.
Failure to establish the range representation means no framing improvement;
it must not reject or strengthen the logical application itself. Recognize an
empty interval only when its emptiness is checked; unknown ordering is not
proof of emptiness. No loop over the numeric range is permitted.

The essential boundary test is a store of one int32 at the exact upper
endpoint. Once the byte representation is justified, that store is outside
the half-open interval. Wider writes, writes through aliases, and writes that
partially overlap its last cell require byte-level exclusion checks. Distinct
parameter names establish no separation. A call's checked write set can be
used through the same rule; an unknown write set cannot be guessed disjoint.

Use the existing distinction between definitional naming and proved framing:

- Assumption-free snapshot normalization may cross only effect edges whose
  separation and representation facts it can justify without ambient premises.
- If a bound or separation premise is required, select it through the indexed
  proof context and retain a checked framing derivation. Do not put that
  context-dependent result into a global assumption-free term cache.
- Old facts remain facts about their original snapshots. A framed application
  equality is the bridge to the later snapshot; neither snapshots nor frozen
  scalar arguments are relabeled globally.

Allocation changes, free, lifetime end, unresolved reallocations, and effects
without a checked write set retain the existing conservative behavior. A small
read range is not a reason to bypass those checks. Empty or unreadable logical
reads grant no authority to cross a lifetime boundary in the initial version.

## Delivery sequence

1. Build the kernel checked-summary constructor and instantiate the supported
   interval. Test complete read coverage and conservative fallback before
   changing any surviving-fact behavior.
2. Add the checked application-framing rule and connect it to explicit
   `transport` using the existing surface syntax. Extend that judgment to this
   Integer application shape if necessary. This makes the proof authority and
   its bounds reviewable independently of automatic naming.
3. Connect checked support to application construction and statement effects,
   so the sweep's unchanged prefix value can be reused automatically. Pure term
   comparison must not start searching for frame proofs. Implement reusable
   range epochs or equivalent persistent effect summaries before accepting an
   automatic path that rescans the entire memory history per application.
4. Remove only the obsolete prefix-frame scaffolding in the unchanged sweep C
   example. Preserve its append proof and the DFS point-update proof. Run full
   verification, expansion, independent verification of the expansion, and
   profiling before integration.

Steps 1–2 are a useful first implementation chunk. Step 3 is the representation
work and deserves review before calling the feature automatic. It need not wait
for the other DFS proof-ergonomics tasks, and it should not be bundled with
shared lemma libraries or generalized quantified transport.

## Acceptance and regression matrix

Positive tests must cover an unchanged prefix after an endpoint store, a store
below a nonzero lower endpoint with checked bounds, an empty fold, a disjoint
write through a proved-separated alias, repeated eligible reads in both
conditional arms, and historical scalar endpoints. Include exact restatement
of the resulting application equality in surface syntax.

Negative tests must cover a write inside the range, a wider partial overlap,
an alias without separation evidence, changed endpoints or base pointers,
changed historical snapshots, missing byte-extent bounds, a changed function
body under the same name in a new session, free/lifetime changes, and each
unsupported read pattern listed above. Test that a logical equality still
cannot discharge a real C access or initialization obligation. Include a
comparison with a function that uses the same array but reads outside the
fold range, to catch accidental narrowing of the array itself.

Pin deterministic work at multiple input sizes along independent axes:
function-definition size, number of applications, unrelated facts/definitions,
and length of a sequence of unrelated stores with repeated application checks.
Summary checking is linear in the selected body; instantiation is proportional
to its small template and arguments. Indexed proof lookup must ignore unrelated
facts. Across a straight-line sequence, range-effect work must be approximately
linear up to indexing factors, not quadratic history walks. Verification must
also be independent of the numeric interval length. Follow
`docs/internals/verification-efficiency.md` and judge green with
`scripts/check.sh`.

## What is settled and what needs an implementation review

Settled in this proposal: no new syntax; total logical terms stay total;
application-specific, kernel-checked summaries; conservative fallback; explicit
framing before automation; and the narrow fold subset above.

The remaining implementation decision is how to retain and index a checked
range epoch alongside the current whole-block array naming without losing
sharing or mixing assumption-dependent evidence with definitional equality.
Validate that representation with the repeated-store scaling test before
expanding the supported language. General helper composition and user-written
read contracts are intentionally deferred.
