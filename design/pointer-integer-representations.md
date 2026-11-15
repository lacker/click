# Pointer bounds through integer representations

Status: the policy below was accepted in the task conversation on 2026-10-15.
The implementation uses a hidden record for unchanged complete C integers. On 2026-10-16 the user also approved cast-based contracts
for full packed-pointer relationships, using existing syntax such as
`requires ((word & ~1) as (struct node *)) == p;`. Their implementation and checked tagged-word transport are in
[PR #1245](https://github.com/clicklang/click/pull/1245). No new `represents` predicate is approved.
This extends [pointer subobject extents](pointer-subobject-extents.md)
and does not close its tracked bug.

## Accepted policy

A lossless pointer-to-integer-to-pointer round trip preserves the original
pointer's allocation origin and selected extent. Equality of integer addresses
alone never supplies either. Keep ordinary integer equality numeric. Keep the
separately approved character/void cast behavior; integer casts do not acquire
that widening rule.

C11 leaves integer-to-pointer conversion implementation-defined. This is
Click's conservative LP64 verification policy, not a claim that C specifies
one universal provenance model.

## Implementation

`CValue::PointerInteger` separates an ordinary signed or unsigned LP64 numeric
value from its original complete pointer. Direct casts back recover that
pointer and its selected extent. Assignment, complete stores/reloads and
whole-value copies retain the record. Changes of integer format and ordinary arithmetic discard it. Checked low-bit
tag operations retain the source pointer; the tag must be cleared before the
value is used as a pointer. Bounded variable tags work in either OR operand
position. Positive constant tag addition on an incoming word requires its low
bit prefix to be clear, preventing carries into the pointer. Addition by zero
and additions with an unknown carry discard the record. Numerical equality never supplies a missing record.
Integer observations in specifications project only the number, so model
functions and numeric resource parameters cannot transport pointer authority.

An untracked nonzero integer with a checked address form can still reconstruct
that address for C comparisons, but receives a fresh opaque designation from
the execution's bounded identity allocator and no original bounds. This identity
is never interned by integer bits or merged by numeric congruence. An incoming parameter, modular result or complete typed word read now carries
its own opaque identity. An explicit specification cast names its reconstructed
pointer, so a contract can constrain that identity without first proving a
numeric address equation. Numeric expressions and model integer fields have
no such carrier.

## Implementation status

Complete pointer read domains track all eight bytes, while numeric pointer
coordinates retain their existing representation. Cached scalar observations
have a no-write memory edge. A producer-retained unchanged-byte source lets
new observations skip prior cache entries directly; upper-half overwrites
invalidate the old bounds. Logical pointer names retain only their exact typed
producer's definition, with specification observations scoped separately from
program facts. Scalar-prefix names cannot supply a complete pointer read.

Complete-pointer comparisons can recover one actual whole-pointer store when
an untouched opaque read denotes a value copied from another cell. They do not
recursively chase records, recover metadata from a stopped scalar-prefix cache,
or undo explicit byte/void views and member selection. Framed read comparisons
follow checked no-write prefixes until their memory sources meet, and stop
before unrelated shared history. Retained coordinate names use their exact
typed-read definitions; arithmetic resemblance is insufficient. Scaling
regressions vary unrelated facts, definitions, cells and history across
16, 64, 256 and 1,024 entries.

Quantified read instantiation retains the original byte width at the rewritten
address before canonicalization. This prevents a four-byte scalar load from
falling back to the eight-byte footprint of a pointer coordinate, and restores
the unchanged arena proof.

Character-pointer identity and signedness casts preserve their incoming bounds,
as approved on 2026-10-16. Other authored pointer-to-character casts and every
authored cast to `void*`, including identity casts, widen to the enclosing
object. Compiler-inserted conversions preserve the incoming view.

Validation covers the ordinary library, deterministic scaling, Markdown and
reference-documentation suites. Seven cast/copy fixtures also check fresh,
expanded and retained verification. The affected nightly coverage is selected
by name: the complete `rbtree-erase` project and four parent/sibling-link
mutation refusal controls. The full nightly suite is not a
per-PR check; the PR records the exact completed checks.

Typed reads recover complete stored pointers once, at the load producer.
Entry normalization then adopts explicit full-pointer premises without repeating
that memory-history search. Its scaling regression keeps work bounded beside
16, 64, 256 and 1,024 unrelated caller resources. Source spelling detects a
repeated pointer query in the same live environment and tries other names;
a small-stack regression checks cyclic candidates and a later valid local.

The complete general erase and rotation-helper proofs retain full cast
relationships in packed-parent resources. The color-repair sidecar verifies all
38 selected proofs within the default budgets. Its mirrored rotations carry
unchanged full-pointer field relationships explicitly. The engine reuses
checked statement effects, indexed constructor contexts, and checked exit
contexts instead of deriving them again. Predicate refutation uses indexed
scalar comparisons instead of searching unrelated memory equations. Each
performance change has a deterministic scaling regression.

The C implementation and verification limits are preserved. The remaining
unseen-pointer formation checks are described in
[Phase C](pointer-subobject-extents.md#phase-c-pointers-of-unseen-formation).

## Reproduced escape

`mdtests/a_pointer_integer_round_trip_keeps_its_subobject.md` converts
`&pair->first` to `unsigned long`, casts back, and reads element one. The
upstream implementation accepts this undefined dereference. The ordinary
mdtest expects rejection and now passes. Keep the original C and both
field permissions in the regression.

The existing `PointerAddress(Box<Pointer>)` records only a physical address.
`cast_tagged_address_to_pointer` can also recover that address from a numeric
word equality. Reconstructing `CPointerValue::new` then loses the selected
extent. Merely putting the full pointer in that term is insufficient: numeric
rewrites, pure-function congruence and resource argument matching could copy
its bounds to another equal integer.

## Approved cast-based contracts

Use existing full pointer equality, without adding a predicate:

```click
requires (word as (int32 *)) == p;
```

Under Phase B this states designation equality as well as address equality.
A tagged word can use the corresponding masked cast. Evaluation must be able
to name an opaque reconstructed pointer before its origin is established;
otherwise this spelling would circularly require the relation it is declaring.
Numeric rewriting of the word must not rewrite that opaque origin. The frontend and evaluator now support this spelling. Ordinary tests cover
incoming words, local copies, whole stores/reloads, partial overwrites, saved
historical values, selected scalar bounds, and explicit modular postconditions.
The basic incoming-word, member-read and modular-call claims also expand and
verify independently. Recursive resource witnesses use the same cast equality;
the original marked-list project now verifies without C changes. The loop case and numeric-observer compatibility checks now pass the ordinary
suite. The packed-parent rbtree proofs use the same relationship.

Logical caches retain numeric observations. Complete reads construct their
opaque word identity from the actual eight-byte source, so caching does not
change physical memory or create a stored pointer representation. A logical
cast names that value independently of its own assumed relationship; execution
may then adopt bounds from full-pointer premises and choose numeric coordinates
from ordinary address equations. These are separate operations.

A resource's numeric word key observes its bits. When its contract also needs
the complete decoded value, pass that value as a pointer argument, for example
`owns h: held(w, w as (struct node *));`, and relate that pointer parameter to the
resource's model. Pointer arguments preserve designation and bounds. A fact
about a word stored in memory can name that storage directly, as in
`fact (p->parent_word as (struct node *)) == q;`.

Resource-body publication and hypothetical arm checks request numeric word
observations before loading. `WordRepresentationScope` avoids recovering a
carrier that those observations discard. Explicit pointer casts restore whole
value demand, including casts nested inside a numeric observation. Fold checks
and ordinary proof expressions retain whole reads: their current numeric
framing can depend on the stored producer's value, as the general erase
store/call/reload control demonstrates. Do not broaden the numeric demand to
those checks without preserving that identity.

The latest scoped full-pointer premise retains its predecessor equality graph.
Withdrawal uses exact persistent fact-map roots to restore that predecessor
without rebuilding unrelated classes. Interleaved withdrawals continue through
the existing rebuild path; this optimization does not make all graph deletion
constant-time.

A distinct representation-bearing word type is another alternative. It makes
full-value transport explicit but changes substantially more model and contract
interfaces. Ordinary mathematical integer values and equality must remain
numeric whichever spelling is chosen.

## Representation and proof boundary

Keep each complete C integer's bits and representation carrier separate.
The carrier is a complete source pointer or an opaque incoming/loaded word
identity. It is not an address-indexed registry, and numeric classes never
choose a carrier. Copying, binding and complete stores/loads transport it.
Partial writes invalidate it; supported complete representation copies retain
it. New allocation producers establish their own known allocation extent.

Arithmetic changes the numeric component. Preserve a pointer carrier only
through the checked lossless tag operations; a zero-tag cast back returns the
same pointer designation. If an operation loses the carrier, an address may
still be recoverable for comparisons, but dereference requires an explicit
representation relation. Do not reconstruct a known allocation extent merely
because the recovered physical block happens to be concrete.

Numeric equality rewrites change numeric components and leave existing
carrier identities intact. Lexical substitution of actual C values transports
both components. Specification integer functions and ordinary integer model
fields remain mathematical: their numeric congruence does not transport a C
representation carrier. A resource that needs one names the actual C word
observation and the pointer model, rather than inferring it from an ordinary
integer argument.

The cast relationship uses its own full-value origin index, with
exact support and scoped withdrawal, independently of the numeric equality
graph. Reading through equal storage addresses may identify a complete word
read; equating the loaded numbers may not. Carry producer-issued full-value
facts through calls, states and proof expansion. Never re-walk or validate
a producer's output in the same session.

## Required controls

| Case | Result |
| --- | --- |
| Member pointer to word and back, reading the member | Accept |
| Same round trip, reading its sibling | Reject |
| One-past member pointer round trip without dereference | Accept |
| Whole word local copy, store/reload, aggregate copy | Retain designation |
| Tag then clear supported low bits | Retain designation |
| Equal numeric addresses with different selected extents | No bounds transfer |
| Numeric equality rewrite, pure function or integer model argument | No bounds transfer |
| Entry word constrained only by its numeric address | No dereference authority |
| Entry word constrained by full cast equality | Adopt the stated designation |
| Callee returns a word with only numeric equality | No bounds transfer |
| Callee explicitly preserves full cast equality | Retain designation |
| Partial overwrite followed by reconstruction | No retained carrier |
| Withdrawal of the only representation premise | Revoke its bounds relation |

Run these in fresh, expanded, rewritten and retained checking. Add deterministic
multi-size tests for selected word-origin lookup and withdrawal beside unrelated
words, facts and memory ranges. Run all ordinary scaling tests and affected
pointer-tag/rbtree fixtures. Phase C adds formation and selection checks for
unseen pointers using the complete identities this phase preserves.
