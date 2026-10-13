# Unchanged adler2 crate adapter trial

Click imports the complete selection rooted at `adler2::adler32_slice` and
proves the four-lane helper bodies and the unchanged general computation.
For every input length zero through 2,147,483,647 bytes from any canonical
initial state, `Adler32::compute` terminates, preserves input bytes, and stores
both fields equal to the shared checksum specification on the entry snapshot.
The proof follows actual native remaining counts, checked signed observations,
and shared input views through all original loops, reductions and final stores.
The unchanged `adler32_slice` entry point composes the checked constructor,
general update and getter and returns the specified packed checksum over the
same length range. A locked real Rust client proves two consecutive updates
equal the full-input checksum for every valid split over that range, preserving
all bytes. A second client proves the same result after saving the prefix
checksum and restoring a fresh receiver before continuing.

The 2,147,483,647-byte limit comes from the bound library
([`bounded-count.click`](bounded-count.click) and the proofs built on it), which
states counts over `int32` and reads each `usize` count through
`((count as u32) as i32)`. The kernel no longer needs it: a 64-bit count bounds a range
and indexes memory directly (`design/typed-indices.md`). Extending the
specification and count/index lemmas to full-width indices would lift this
proof limit.

The function contracts use Rust syntax (`docs/reference/rust.md`,
"Signatures in Rust syntax"): `fn` signatures, `impl` blocks, paths such as
`adler2::algo::U32X4`, `bytes.len()` and `p.f`. Proofs use `have P;` and
`by T(args);` for single steps. The standalone theorem libraries keep Click's
numeric types and casts because the same lemmas also check C proofs.
Rust sources require this function spelling; C-shaped signatures and reference
fields written with `->` are refused.

The two files in `src/` are byte-for-byte copies of adler2 2.0.1, revision
`89a031a0f42eeff31c70dc598b398cbf31f1680f`. Their hashes match the
[source manifest](../../rust-checksum-sources.json). The original 0BSD license
is included. Neither modules, derives, methods, operators, nor loops were edited.

## Current checked boundary

Schema 4 locks the Rust-2021 crate root, `std` feature, selected entry point,
and complete rustc dep-info closure. Both module files enter the prepared
identity. Missing, extra, changed, escaping, or symlinked inputs are rejected.
Qualified declaration identities distinguish module functions, inherent
methods, and concrete assignment-operator implementations.

The `click-charon-crate-v4` adapter imports the original reachable computation,
including `Adler32::compute`. Constructor regressions prove that the actual
`Adler32::default` and `Adler32::new` bodies return `a = 1`, `b = 0`. Scalar
initializer contracts prove `MOD = 65521` and `CHUNK_SIZE = 22208` by executing
their imported CFGs.

The [helper sidecar](helpers.click) uses the [locked configuration](helpers.click.import.json)
and native Charon artifact to prove every lane of these original helpers:

| Body | Contract |
| --- | --- |
| `U32X4::from` | At least four bytes and a shared view of the first four; each returned lane equals its corresponding input byte and is at most 255; each unsigned Integer observation equals its entry byte’s signed Integer widening and lies in `0..255` |
| `AddAssign<Self>` | Each Integer lane sum fits u32; each output lane equals its old value plus the corresponding by-value operand, with exact Integer sum and nonnegative observation |
| `RemAssign<u32>` | Nonzero divisor; each output lane equals its old value modulo the divisor, has the exact unsigned Integer remainder observation, and lies in `0..divisor-1` |
| `MulAssign<u32>` | Zero multiplier or each lane fits the quotient bound; each output lane equals its old value times the multiplier, with exact Integer product and observation in `0..4294967295` |

Mutating helpers require ownership of all four receiver lanes. Addition accepts
Integer sum bounds and derives the widened `(int64)` Rust overflow guards;
it permits the full safe u32 domain. Multiplication's disjunction includes a zero multiplier
without evaluating division by zero. These proofs establish the access and
panic prerequisites in the helper bodies, conditional on their contracts.
The whole-body bounds proof establishes those prerequisites at the actual
helper calls in every batch and remainder.

The constructor also exports `0 <= to_integer(lane) <= 255` for each lane.
Its proof applies checked unsigned-order bridges to the actual returned
fields, making the byte bounds usable by the Integer lane-step lemmas. The
bridges retain the full u32 range; signed reinterpretation would be unsound
for accumulated B lanes above the sign bit.

[Lane-state lemmas](lane-state.click), assembled after the common specification,
observe `a + sum(a_lanes)` and
`b + 4 * sum(b_lanes) + 6 * MOD - a_lane_1 - 2 * a_lane_2 - 3 * a_lane_3`
in Integer arithmetic. A checked four-byte step gives the ordered B weights
`4,3,2,1`; reducing the lanes preserves both residues. The B reduction requires
a nonnegative representative and permits a negative congruence witness.
Checked one- and four-byte prefix lemmas connect the A residue recurrence to
the common specification. A four-byte B prefix lemma proves the ordered weighted
update against the same specification, with explicit index and nonnegative
representative bounds. These are mathematical lemmas, not a verified
summary of the general computation: its nested-loop checksum induction remains
incomplete. Native `viewable(bytes[0u64..bytes_len])` observations now name the
same full-width range as the shared resource clauses and retain its byte-extent
guards. Checked transport carries an exact liveness range across stores without
widening it or claiming preservation of its contents. The helper’s exact entry-byte observations supply the correspondence
needed at each original vector-construction call.

The remainder helper exports the strict native and Integer divisor bounds
for all four lanes, along with nonnegative Integer observations. Its original
`%=` body proves those guarantees for every nonzero u32 divisor. Specializing
the call to `MOD = 65521` yields the `0..65520` range needed to reset both
lane ceilings before a new batch. The general computation proof checks this
reset and preserves the ceilings over the original outer loop.

The exact remainder observation uses checked `uint32_remainder_to_integer`
bridges on the entry lanes. A source-proved lemma derives the Integer
nonzero domain from the native nonzero divisor; callers supply no additional
mathematical precondition. Division has the corresponding checked unsigned
bridge. The common specification proves residue congruence with a signed
quotient witness, so subtracting weighted lane reductions can preserve a
checksum even when that witness is negative. The general contract combines these observations with the actual loop and
store proofs to establish both final checksum fields.

The multiplication helper also exports the exact Integer product for each lane.
`uint32_multiply_to_integer` uses the original native quotient guard, including its
zero-factor branch, to justify the non-wrapping observation. This lets caller
proofs carry numeric lane ceilings through the original `*=` body: for example,
a reduced lane at most 65520, multiplied by four, has an Integer observation at
most 262080. The theorem covers the full unsigned range; defined wrapping
multiplication alone cannot justify an exact mathematical product. Kernel
regressions check unsigned boundary values and both sides of the last safe
quotient. Helper regressions reject false products/bounds and missing guards
independently for every lane. The four-byte caller proof below uses these bridges.

Frozen and live regressions check the original source hashes, prove all four
helpers, and reject false lane claims, short reads, missing safety guards,
wrapping addition bounds, and mutation under a shared view. CLI verification,
profiling, auditing, and expanded certificates must agree. These tool rechecks
run in the nightly suite; direct verification and rejection tests stay in the
ordinary gate.

## General batch metadata

[General partition lemmas](general-partition.click) cover nonnegative lengths
through `INT32_MAX`, the current memory-index boundary. They relate full-width
Rust metadata to signed indices, split a four-byte prefix into full 22,208-byte
batches and an aligned remainder of at most 22,204 bytes, and establish the
actual outer iterator's nonempty-step bound, divisibility and strict progress.
A checked access lemma combines a batch's absolute start with the inner
cursor displacement to keep the four-byte read inside the original input,
including at the signed-index boundary. Native additions use checked Integer
bridges and preserve their overflow prerequisites. A cursor-step lemma
relates the original pointer advance to the decreasing outer remaining count;
its pointer equalities grant no memory authority.
The bounded-slice access lemma uses the actual final-batch length rather than
requiring room for a complete batch. It preserves the nested signed additions'
definedness even when the last four-byte read ends at `INT32_MAX`.
A signed partition identity proves that the full-batch prefix and aligned
remainder reconstruct the original prefix without overflowing. The exhaustion
lemma reasons from the stored size comparison in the actual iterator exit
disjunction. A native C guard regression checks that control-flow shape and its
decreasing remaining count; it is independent of the Rust computation proof.
No generated processed counter is used. The general computation proof
composes these lemmas with the original outer-loop invariant; they do not
establish checksum correctness.

## Lane batch arithmetic

The [bounds library](bounds.click) checks the mathematical ceilings proposed
for the lane-loop invariants after `n` four-byte vectors since the last
reduction:

```text
A(n) = 65520 + 255*n
B(n) = 65520 + 65520*n + 255*n*(n+1)/2
```

Checked product and truncating-division certificates establish the triangular
term's bound for every `n` in the batch range. At `n = 5552`, the ceilings are
`A = 1481280` and `B = 4294690200`; the latter leaves 277095 below `u32::MAX`.
At `n = 5553`, `B = 4296171735` exceeds u32. Initial ceilings cover reduced
lanes, and a byte of at most 255 preserves both successor bounds:
`a + byte <= A(n+1)` and `b + (a + byte) <= B(n+1)`. The triangular
successor identity and `B(n+1) = B(n) + A(n+1)` are checked with bounded
polynomial and nonnegative quotient-shift certificates. Given the
proposed `A(n)` and `B(n)` bounds and `n < 5552`, the next two additions remain
nonnegative and below the full-batch ceilings. The range is per batch; it
imposes no bound on the total number of batches in an input.

The native lane-step lemmas now compose those ceilings with unsigned Integer
observations to establish the widened `int64` addition guards in the original
`U32X4::add_assign` body. Its sidecar now accepts the corresponding Integer
no-wrap bounds and exports exact Integer sums and nonnegative observations
for all four updated lanes. The checked addition bridge discharges the native
overflow guards without changing the original body. Checked no-wrap bridges
prove that the updated native A and B lanes have the mathematical sum values and satisfy their successor
ceilings. In B's update, the operand is the newly updated native A lane.

These are checked arithmetic implications. They do not yet establish the
lane bounds over the original iterator states or prove checksum correctness. The tests check
the bounds alongside the actual helper contracts in one prepared environment,
and reject a larger batch, missing bounds, false endpoints, altered product
or quotient certificates, altered recurrence coefficients, reversed quotient-shift
guards, and false A- or B-invariant steps.

## Recombination arithmetic

The [recombination library](recombination.click) proves exact Integer values
and overflow guards for the original expressions `b + (MOD - a)`,
`b + (MOD - a) * 2`, and `b + (MOD - a) * 3`. Given a reduced A lane below
65521 and a B lane already multiplied by four with observation at most 262080,
the respective ceilings are 327601, 393122, and 458643.

The checked `uint32_subtract_to_integer` rule requires the native unsigned
no-underflow guard. It relates `MOD - a` to `65521 - to_integer(a)` across the
full unsigned domain. Defined unsigned subtraction alone permits wrapping.
Regressions check the bridge's actual machine guard and observation against an
independent boundary model, executed C subtraction, expanded certificates,
missing bounds, and false lane weights or ceilings.

These are conditional arithmetic proofs checked alongside the original helper
contracts. They do not establish the premises at each original recombination
site or prove the complete four-byte checksum by themselves. The four-byte
caller proof below supplies those premises; general initial states and
preservation over larger nonempty vector batches remain open.

## Native cursor and signed byte observations

[count-bridge.click](count-bridge.click) checks that a native `uint64` count
at most 22,208 denotes the same byte address as its signed index observation.
The proof first establishes equality of their exact Integer values, then
cites that equality to `normalize`. Both index widths remain intact; a
truncated low word alone does not establish the address equality. This bridge
also proves that reads at those addresses have equal byte values and equal
Integer observations. For a chunk beginning at a native count through 22,204,
it connects each of its four positions to the signed specification index,
with checked guards for the signed addition. The proof establishes native read
equality before rewriting the Integer observation; address equality alone does
not normalize the Integer loads. Complete claim audits, expansion and cold
re-verification check both observation lemmas; mutations reject shifted byte
positions and missing count or lane bounds. The remaining-count bridge recovers
the chunk just consumed by `Next` at `prefix - remaining - 4`, with native and
signed subtraction bounds. It verifies, expands and re-verifies; mutations
reject shifted chunk starts, wrong lane positions and missing guards.

The original small-batch vector loop explicitly recovers all four constructor
lanes from its shared subslice, uses the checked byte-cast lemma to obtain
their Integer observations at the constructor mark, and connects each lane to
`bytes[prefix - remaining - 4 + lane]`. The position comes from the actual
stored remaining count after `Next`; no processed-count local is introduced.
Native byte equality precedes the Integer equality chain, which uses three
explicit arithmetic premises. The unchanged whole computation verifies with
these observations. Nightly mutations reject a shifted subslice and a lane
associated with the wrong input byte. Carrying both checksum residues through
the original loops remains necessary.

## Native vector-prefix transitions

[vector-prefix.click](vector-prefix.click) connects the joint optimized lane
transition to both common prefix residues for arbitrary byte values and
canonical A seeds. Its native bridge checks each `uint32` addition guard and
uses the constructor's exact byte observations. The scalar B representative
accounts for the deferred chunk contribution, retaining the original weighted
lane recombination and modulus offset.

The iterator adapter derives the prefix from `total - remaining` for a batch
through 22208 bytes and advances it by consuming four bytes. It also proves
that the remaining length stays within bounds. No processed-count local is
introduced. Verification, profiling, focused audit, expansion and cold
re-verification check these transitions; mutations reject wrong bytes, missing
addition guards or residue premises, changed seeds and incorrect cursor steps.
These are checked transition lemmas. Establishing and carrying their premises
through the original nested loops, reductions, recombination and final tail
remains necessary for general-length checksum correctness.

## Index derived from iterator state

The [iterator bounds library](iterator-bounds.click) observes the existing
signed remaining-byte state as
`N(total, remaining) = truncating_quotient(to_integer(total) - to_integer(remaining), 4)`.
For a batch of at most 22208 bytes, with `0 <= remaining <= total`, it proves
`0 <= N <= 5552`. If at least four bytes remain, `N <= 5551`, the native
`remaining - 4` operation is defined, and consuming four bytes advances N by
exactly one. No processed-count local is introduced.

The native lane-step lemmas now compose with this derived index. Under the
A/B bounds at N and the byte bound, both addition guards hold and the updated
native lane observations satisfy the A/B ceilings at
`N(total, remaining - 4)`. Initial, empty, short-tail, small exact-multiple,
and final full-batch indices have checked endpoints. The library has 16 theorem
groups with 34 checked conclusions; verification, profiling, auditing, and
expansion recheck them alongside the existing arithmetic dependencies.

The stored traversal length is `int32`, with range checks at construction;
the source slice's length remains `uint64`. The proofs use the traversal
observation directly rather than treating the slice length as an iterator
counter. A checked initialization theorem establishes both ceilings from
reduced lanes at `N(total, total) = 0`. Another theorem exports the exact
Integer-sum requirements of the original `AddAssign` calls for both `a + byte`
and `b + (a + byte)`.

The four-byte caller proves a terminating symbolic loop over the original
remainder-vector iterator. Its invariant uses the actual cursor, remaining
length and chunk size, preserves both owned lane arrays and the input view,
and relates every lane to the corresponding original byte at exhaustion.
The preserve proof executes both original helper calls, checks their numeric
requirements and closes the back-edge claims. Its verification unit checks
the iterator and lane lemma bodies alongside every original helper body.
Its final A and B fields equal the common mathematical specification on the
four entry bytes, starting from A = 1 and B = 0.
[The native recombination bridge](four-byte-spec.click) checks every unsigned
addition, subtraction, multiplication and remainder, then removes the six
multiples of 65521 in the original B expression. It preserves the ordered
weights 4, 3, 2, 1; reversing the middle weights is rejected. The contract still
covers one four-byte vector. The shared checksum getter is checked below;
correctness induction over larger batches remains to be supplied.

A false byte-order contract exposed expensive premise presentation: each
attempt to name a scalar atom copied every memory-backed local value across
historical snapshots. Scalar-name lookup now checks the recorded load address
first. A smart proof producer may then search declared local slots for a
checked alias, borrowing values and charging every inspected slot. Explicit
certificate validation skips that search and uses the recorded load and memory
epoch. The lookup never materializes unrelated heap storage. Scaling
regressions cover increasing local counts, deep unrelated expressions, and a
million-element seeded range. The caller names its stored cursor, chunk size,
and remaining length explicitly at the head, so the four-byte transition uses those few checked facts.

These implications match the adapter's stored remaining-byte state and
four-byte `next` transition. The single-vector loop establishes and maintains
its numeric bounds, lane bounds and memory view; the original nested loops
over arbitrary batches have the terminating checksum proof described below.

Integer equality evidence now works in either orientation for explicit theorem
applications and fact transport, including observations of native values and
entry snapshots. This repairs the proof interface used to connect the derived
index to iterator transitions; it adds no new loop invariant or checksum claim.


## Original empty-input computation

The same [locked sidecar](helpers.click) now checks the unchanged
`Adler32::compute` body with an empty input and initial state `a = 1`, `b = 0`.
It requires ownership of both state fields and a shared empty input view,
and proves both output fields: `a = 1`, `b = 0`. All four helper contracts and
both constant getter bodies are verified in the same file.

The proof checks the original scalar addition and modulo, lane recombination,
ordered shared array iterations, final modulo results, and narrowing stores.
For this input the recombined B lanes are `0`, `65521`, `131042`, `196563`;
their sum is `393126 = 6 * MOD`, which reduces to zero. Snapshot equations and
explicit rewrites retain the actual operand values. The proof names a few
adapter capture locals to cite original call results directly; it introduces
no source variables, processed counter, assumed loop invariant, or proof hole.
These low-level names are tied to the frozen import and must recheck after
adapter changes.

The complete boundary proof and false-output rejections take longer than a
few seconds and run in the nightly suite. Missing empty-input, scalar B, and
ownership prerequisites are ordinary regressions. Nonempty chunk/tail
preservation, arbitrary initial-state preservation, and the general checksum
contract remain later work.

## Original single-byte computation

[single-byte-compute.click](single-byte-compute.click) checks the unchanged
`Adler32::compute` body with one arbitrary byte from the constructor state
`a = 1`, `b = 0`. It owns both state fields, borrows the input, and proves that
the input byte is preserved. The final field observations are checked in the
original modulo form: `a = (1 + byte) % MOD` and
`b = (6 * MOD + 1 + byte) % MOD`. For a byte in `0..=255`, these are the
single-byte checksum values `a = b = 1 + byte`.
The contract also proves that both fields equal the
[shared specification](../../adler32-spec.click) on the entry byte snapshot.
Checked unsigned remainder bridges and signed-witness congruence remove the
`6 * MOD` offset. This focused connection covers one byte from the constructor state; the
general contract below covers all supported lengths and canonical seeds.

The proof follows the stored serial iterator, identifies its read with the
original byte, bounds both additions, and checks the final modulo and `u16`
stores. The kernel cast-identity rule recognizes both canonical nested casts
and the exact unsigned masks used by byte readback, with explicit destination
range bounds. No Rust source, extraction artifact, lock, or import profile changes.

This file is a contract fragment. Function-contract imports between Click
sidecars are not admitted yet, so the fixture harness combines it with the
canonical helper and constant-getter contracts from `helpers.click`, the common
specification, and checks their proofs. This preserves the empty-input sidecar and avoids
duplicate helper interfaces. The full positive proof, false checksum and
byte-preservation claims, missing length/view and empty-input rejections, and
verify/profile/audit/expansion rechecks are nightly tests. The original-body
checks exceed the ordinary per-test budget.

## Original two- and three-byte serial tails

[two-byte-compute.click](two-byte-compute.click) and
[three-byte-compute.click](three-byte-compute.click) extend the constructor-state
proof to arbitrary inputs of length two and three. Every original serial read
is identified with its input position. After read `j`, the stored cursor is
`old(bytes) + j` and its remaining count is `length - j`; no processed-count
local or assumed loop invariant is introduced.

Each iteration proves the native recurrence `A_j = A_(j-1) + byte_(j-1)` and
`B_j = B_(j-1) + A_j`, starting from `A_0 = 1`, `B_0 = 6 * MOD` after the
unchanged lane recombination. The checked upper bounds for A are 256, 511,
and 766, and for B are 393382, 393893, and 394659. These discharge both
original overflow checks on each pass. The final field observations equal
the native `A_length % MOD` and `B_length % MOD` expressions through the
original `u16` stores, and every input byte is preserved.

The same fixture assembly checks the canonical helper/getter bodies alongside
each computation fragment. Nightly regressions reject false A/B results,
changes to each preserved byte, swapped byte weights in B, and repeated reads
of a preceding byte. Verify/profile/audit/expansion recheck both contracts.
Missing length/view, wrong extent, and wrong constructor-state premises have
ordinary rejection checks. Rust source, extraction artifacts, locks, and the
import profile remain unchanged.

## Original shared checksum getter

[checksum.click](checksum.click) proves the unchanged `Adler32::checksum`
body for any two `u16` fields. Shared views of A and B suffice; neither field
changes, and the Integer observation of its returned word is exactly
`65536 * B + A`. The contract imposes no constructor or canonical-seed condition.

[packing.click](packing.click) checks the narrow-field observations and the
original `(B << 16) | A` order. Both 16-bit bounds are retained in the kernel
packing law. Its conditional bridge connects fields satisfying the common A/B
specification to the common packed checksum. The zero- through four-byte
public entry points and general-length composition are checked below.

The fixture harness combines these contract fragments with the shared
mathematical specification and the existing locked crate import. The positive
original-body proof runs in the ordinary gate. False packed results, missing
shared authority, and verify/profile/audit/expansion agreement run nightly:

```sh
cargo nextest run --test rust_import --run-ignored all \
  -E 'test(charon_adler2_checksum)'
```

## Real incremental client

[incremental.rs](incremental.rs) is a new client of the unchanged pinned library.
It splits one input slice, constructs an `Adler32`, performs the original
`write_slice` on each half, then calls the original checksum getter. The two
library files remain byte-for-byte pinned; the client re-exports `Adler32` so
the original `algo.rs` crate-root import resolves without editing the library.

[incremental.click](incremental.click) proves the common full-input packed
checksum and byte preservation for every length zero through 2,147,483,647
and every split from zero through that length. This includes empty inputs,
empty prefixes/suffixes, exact batches and scalar tails without fixing concrete
lengths in the proof. The lock includes the client and both original module
files, with the sole root `adler_incremental::incremental`.

The harness reuses the existing computation, constructors, public update and
getter fragments under their new qualified module paths and checks their bodies
in the same unit. [incremental-split.click](incremental-split.click) connects
native split lengths to signed concatenation observations. The update contract
exports native canonical seed bounds so its result meets the next call's
preconditions. A pointwise suffix-address proof and extensionality connect the
actual shared subslice to the logical concatenation suffix; frozen field
observations connect the second call's seeds to the first call's results.

Focused caller verification, false checksum/authority/split/preservation checks,
complete original callees and client-contract expansion/reverification run nightly:

```sh
cargo nextest run --profile nightly --test rust_import --run-ignored only \
  -E 'test(charon_adler2_incremental_client) | test(adler_incremental_bridges)'
```

This client continues in the same receiver. The saved-checksum client below
checks restoration into a fresh receiver before the second update.

## Saved-checksum constructor

[restoration.click](restoration.click) checks the unchanged
`Adler32::from_checksum` body for every `u32` checksum, without a canonical-seed
precondition. Its exact observations are:

```text
(result.a as u32) == old(sum & 65535u32)
(result.b as u32) == old((sum >> 16) & 65535u32)
```

The contract describes the Rust program's truncating casts with masked words.
Proof-expression narrowing casts instead require representability; using
`sum as u16` in the specification would impose a different condition. The
native Charon artifact locks both original module files and the qualified
constructor root. Tests verify its body, reject lost masks, swapped words and
an incorrect shift, expand and recheck its proof, and refresh the live import.

```sh
cargo nextest run --test rust_import -E 'test(charon_adler2_restoration)'
cargo nextest run --profile nightly --test rust_import --run-ignored only \
  -E 'test(charon_adler2_restoration)'
```

## Saved-checksum resumed client

[resumed.rs](resumed.rs) splits the input, computes and saves the prefix checksum,
restores a fresh receiver through the unchanged `from_checksum`, then calls the
original update and checksum methods on the suffix. Its two source-level
`state` bindings retain their distinct native MIR identities in the proof.

[resumed.click](resumed.click) proves the packed full-input specification and
preserves every byte for all lengths zero through 2,147,483,647 and all valid
splits. It explicitly proves the restored A/B words equal the frozen prefix
fields and satisfy the next update's canonical-seed preconditions. Empty input,
empty prefixes/suffixes, exact batches and short tails are included by these
quantified bounds. Arbitrary saved `u32` values can have noncanonical seeds;
the resumed client restores a checksum produced by a checked update.

The getter exports both its Integer result and the exact native packed word.
Two standard kernel-supported theorems, `uint32_unpack_uint16_low` and
`uint32_unpack_uint16_high`, recover the masked words of `(high << 16) | low`
when both fields are at most 65535. The high-word rule uses a logical right
shift, including when the packed word's top bit is set. Explicit Integer
order bridges carry the canonical 65520 bounds to these 65535 preconditions.
The remainder of the client reuses the checked split, byte extensionality and
concatenation reasoning. No library body or checksum summary is assumed.

The lock covers the new client and both unchanged pinned library modules, with
sole root `adler_resumed::resumed`. Nightly checks verify all assembled original
callees and the client, expand and recheck the client, reject false result,
split and byte-preservation claims and missing view authority, and refresh the
live Charon import before rejecting a changed client input.

```sh
cargo nextest run --profile nightly --test rust_import --run-ignored only \
  -E 'test(charon_adler2_resumed_client)'
```

## Original public entry points

[public-general.click](public-general.click) composes the unchanged
`Adler32::write_slice` and `adler32_slice` bodies with the general computation
contract, constructor and shared checksum getter. Every length zero through
2,147,483,647 returns the common packed checksum on the entry input snapshot
from A = 1, B = 0. `write_slice` also proves both field specifications from
any canonical initial state and returns fields below 65,521. Both contracts
explicitly preserve every input byte. The checked `adler_bounded_signed_index`
lemma bridges each guarded logical index to native 64-bit range membership;
constructor seed observations are frozen and substituted explicitly into the
computation result. The full original computation and all helper bodies remain
in the assembled verification unit; no assumed checksum summary supplies a result.

General composition, false checksums/seeds/extent/authority/preservation, all
original callee bodies, and public-contract expansion/reverification run nightly:

```sh
cargo nextest run --profile nightly --test rust_import --run-ignored only \
  -E 'test(charon_adler2_general_public_checksum) | test(adler_bounded_signed_index)'
```

[public-constructors.click](public-constructors.click) checks the unchanged
`Default::default` and `Adler32::new` bodies in a shared fragment for the public API fixtures.
[public-empty.click](public-empty.click),
[public-one-byte.click](public-one-byte.click),
[public-two-byte.click](public-two-byte.click),
[public-three-byte.click](public-three-byte.click), and
[public-four-byte.click](public-four-byte.click) compose those constructors,
`Adler32::write_slice`, the original computation, and `Adler32::checksum` at
`adler32_slice`. For every input length from zero through four, with arbitrary byte values, the returned
word's Integer observation equals `adler_spec_checksum` on the entry byte
snapshot, with initial A = 1 and B = 0. Every input byte is preserved.
The empty public call also verifies without an input-byte view; it dereferences
no input bytes. The four-byte call exercises the optimized vector path.

The harness assembles these fragments with the matching existing computation,
helper bodies, packing lemmas, and common specification. Complete verification
checks all original callee bodies. The ordinary gate checks the new API bodies;
nightly checks cover complete assembly, wrong results, seeds and extents,
insufficient byte views and false byte preservation, plus focused audit,
contract expansion and re-verification. Full profiling checks the empty, two-, three-, and
four-byte assemblies before expansion. The Rust source and locked Charon
artifact remain unchanged.

```sh
cargo nextest run --test rust_import --run-ignored all \
  -E 'test(charon_adler2_public_)'
```

[serial-tail-spec.click](serial-tail-spec.click) connects the unchanged two-
and three-byte native results to the common field specification. It checks
that each unsigned prefix addition stays within range, retains the ordered B
weights, and removes the native `6 * MOD` offset under remainder. Checked
two- and three-byte specification lemmas unfold the byte and weighted sums.
The computation contracts retain their native results and byte preservation
while also proving the common A/B results. These helpers have expansion and
wrong-weight/offset regressions. General-length implementation correctness is checked by the computation and
public-client proofs above.

## Reproduce

Build Click and pinned Charon with the normal repository setup. The frozen
artifact verifies without extracting again:

```sh
target/debug/click verify design/charon-trial/adler2/helpers.click
target/debug/click verify design/charon-trial/adler2/bounds.click
target/debug/click verify design/charon-trial/adler2/iterator-bounds.click
```

Check the single-byte fragment against the same locked native body and shared
contracts, including proof-tool rechecks:

```sh
cargo nextest run --test rust_import --run-ignored all \
  -E 'test(charon_adler2_single_byte_compute)'
```

Check both new serial-tail fragments and their negative/tool regressions:

```sh
cargo nextest run --test rust_import --run-ignored all \
  -E 'test(charon_adler2_short_tail_compute) | test(charon_adler2_two_byte_compute) | test(charon_adler2_three_byte_compute)'
```

Refresh the entire selected crate through the production adapter:

```sh
target/debug/click import lock design/charon-trial/adler2/helpers.click
```

The configured exporter path is relative to this directory. Run the focused
live regression to refresh a private copy and reprove the original helper bodies:

```sh
export CLICK_CHARON="$PWD/target/charon/debug/charon"
cargo nextest run --test rust_import --run-ignored only \
  -E 'test(charon_adler2_helpers_live_refresh_proves_original_bodies)'
```

## Remaining proof work

Prove the unchanged C implementation and derive C/Rust equality
under matched input and seed conditions. See the
[checksum assessment](../../rust-checksum-assessment.md).

Full original-computation smart audits exhaust the standard ten-minute run bound
before completing a site, although ordinary verification succeeds. This is an
audit-tool limitation; the timeout supplies no proof verdict. Standalone byte
observations pass complete audits, and all helper bodies remain checked alongside
the computation.

## Historical trial

The [result record](result.json) preserves the initial 2026-10-06 single-file
trial. Selected native extraction succeeded, but production schema 3 rejected
the two-file crate before publishing an artifact or lock. Schema 4 resolved
that input boundary; subsequent increments added checked constructors, by-value
operator operands, and scalar constant initializers. The historical result's
rejection is not the current adapter status. Schema-3 configurations retain
their single-file interpretation.

## Arbitrary small-batch induction

The [small-batch contract](small-batch-compute.click) verifies the unchanged
`Adler32::compute` body for every length in `0..22207`, starting from any
canonical state with `a,b < 65521`. It uses the original stored vector and
scalar iterator remaining values and cursors, carries all eight lane ceilings
and the shared input view, and proves termination. It checks the original
reductions, weighted recombination, both four-lane scalar sums, the zero-to-three
byte scalar tail, and final 16-bit stores. Both output fields remain below
65,521. No generated processed count supplies the induction or ranking.

The original vector loop carries functional A and B invariants:
`(a + A0 + A1 + A2 + A3) % MOD` equals the shared A specification at
`prefix_length - remaining`. The proof initializes this relation for the empty
prefix from any canonical A seed, identifies each constructor lane with its
original input byte, and combines the checked native additions with the
four-byte specification recurrence. At loop exit it establishes the relation
for the whole four-byte prefix. Loop closure explicitly checks the signed
prefix subtraction's safety and every invariant and ranking obligation.
B uses the representative
`b + n*a + 4*(B0+B1+B2+B3) + 6*MOD - A1 - 2*A2 - 3*A3`, where
`n = prefix_length - remaining` and the scalar seeds stay unchanged during
this loop. Its nonnegative representative and residue are initialized at the
empty prefix and preserved by the ordered four-byte update. The `n*a` term
accounts for the original scalar contribution deferred until after the loop.
A checked signed-count lemma transports its exact Integer advance, and the
loop exit establishes both residues for the completed four-byte prefix.
A is also transported through the original lane reductions and four scalar
lane additions, establishing its prefix residue before the tail. The proof
uses the helper's native remainder equations and checked uint32 observations
to connect the entry lane snapshot to the reduced values. The original B seed
product and addition now prove the exact deferred `b + prefix_length*a` value,
including preservation of the native length cast. B also passes through the
scalar and lane reductions, all three ordered lane corrections and the four
scalar additions. The reduction proof preserves the nonnegative representative;
native subtraction, multiplication, addition and store checkpoints connect the
actual weighted values to the common B prefix residue. Both scalar residues
pass through the original scalar tail. Its invariants relate the current
A and B words to the common prefix at `length - remaining`, using the stored
iterator state. Each returned byte is checked against its actual post-`Next`
position; the signed prefix advances by one, the native A addition preserves
its residue, and B includes the newly updated A value. Definedness bounds,
byte casts and native assignment observations are explicit checked steps.
The scalar-loop exit establishes the full-input residues. Explicit byte-equality
invariants preserve the entry input through both loops, and checked sum
extensionality connects the current specification to the entry snapshot before
either receiver field is stored. Native remainder equations and bounded
16-bit cast certificates establish both final field postconditions against
that fixed snapshot. No checksum result is assumed. Nightly mutations reject
false final A and B checksum claims, a duplicated lane
byte in the A transition, a changed completed-prefix A seed, an incorrect B
byte weight, an omitted B seed contribution, a duplicated A lane during scalar
recombination, changed recombined-prefix seeds, and an incorrect native B lane
correction weight.

The source-proved one-byte A and B recurrences advance both residues at the
scalar-tail index. The B recurrence includes the updated A contribution. A
native read bridge identifies the byte returned by `Next` using
`length - remaining - 1`, checks its signed-index observation, and rejects
a shifted byte. The original scalar-tail induction applies these lemmas.

The fixture is assembled with the existing helper bodies, recombination
lemmas, iterator bounds, the common specification and lane-state lemmas,
[partition lemmas](partition.click), and [scalar-tail bounds](tail-bounds.click)
by the Rust import tests. The partition
lemmas relate full-width lengths, signed indices, rounded four-byte prefixes,
and the original nested subtraction for the remainder. Tail lemmas justify
both nonwrapping scalar updates and the actual iterator's progress.

Normal tests verify the partition and scalar-tail arithmetic libraries.
Nightly tests expand their claims and reject false ceilings, byte accounting,
divisibility, and progress. Original-body mutations reject missing input
authority, an admitted full outer batch, and either missing canonical seed
bound. Whole-proof verification, tool agreement, and cursor, ranking,
induction, and final-bound rejections also run nightly.
Full outer batches are outside this small-batch contract; the general contract
below covers them and proves both final checksum fields.

## General whole-body induction

The [general computation contract](general-compute.click) verifies the original
body for every length in `0..2147483647`, with canonical seeds `a,b < 65521`.
The signed observation limit is explicit; full-width metadata is not truncated
to admit larger inputs. The proof includes arbitrary numbers of full
22,208-byte batches, the aligned vector remainder, and the scalar tail.
It preserves the original shared input view, checks every native access and
arithmetic guard, and ranks all loops by their actual stored remaining state.
Both final fields remain below 65,521. No assumed checksum summary or generated
processed counter supplies these guarantees.

Each full-batch vector step also proves that all four constructor lanes equal
exact mathematical byte observations at absolute positions in the original
input. The positions come from the stored outer and inner remaining counts.
The [partition lemmas](general-partition.click) check signed addition before
regrouping byte pointers. The proof first establishes machine-byte equality
across the constructor's local return storage, then rewrites the Integer
observation using that equality. These observations supply the input values
needed for the outer checksum recurrence.

The aligned remainder also connects each actual constructor lane to its exact
absolute input byte after any number of full batches. Its stored remaining
count determines the local position, and its cursor invariant retains both
signed and full-width address observations. An explicit constructor-entry mark
uses the helper's checked Integer postconditions; byte preservation transports
those observations to the vector-addition snapshot. [remainder-prefix.click](remainder-prefix.click)
checks the four-byte start and pointer regrouping against the actual window,
including starts near the signed-index limit. Its endpoint lemmas check the
Integer consumed-byte observation at initialization and actual exhaustion.
Shared borrowing retains checked
wide-index aliases beside signed and mixed-index spellings. Missing aliases and
short views remain rejected. The remainder lane loop carries both checksum
residues against the common specification at the global position
`full_batch_prefix + remainder_length - remaining`. Initialization reuses the
completed full-batch residues. Each actual native lane addition advances that
position by four under checked signed-addition guards; B retains its deferred
local-position times A contribution and fixed entry seed. Actual iterator
exhaustion establishes both residues for the complete aligned prefix, including
an empty remainder. The original remainder seed product and scalar B addition
supply the exact deferred contribution. Checked native remainder observations
carry both residues through the lane reductions; the original ordered B
corrections and four scalar sums establish both scalar residues for the complete
aligned prefix. The local remainder length stays distinct from the global
specification position, and the B specification keeps the entry receiver seed.
The native unsigned count bridge is checked independently and expanded with
the remainder-position claims.

The full-batch loops carry both residues against `adler_spec_a` and
`adler_spec_b` at every actual remaining count. Each native four-byte addition
advances the global prefix; each original reduction preserves its residue.
The B seed remains the entry receiver value as Rust updates the working scalar
B between batches. At outer-loop exhaustion the retained scalars and four-lane
state represent the specified A and B for the complete full-batch prefix.
Both loops retain equality of the input bytes with the entry snapshot. The
independent A transition lemmas in [vector-prefix.click](vector-prefix.click)
are reused by the joint A/B lemmas.
The B proof observes the batch-local position from the stored inner remainder
and includes the deferred position times scalar A contribution in its lane
representative. The checked native vector step adds four times the old A
representative and the actual byte weights `4,3,2,1`; its nonnegativity invariant
passes through every original inner iteration. At batch exit, the original
`22208 * a` multiplication and scalar B addition supply the exact deferred
contribution. Frozen observations connect the actual A-lane, B-lane and scalar
remainders to the source-proved B reduction, preserving the combined B residue.
[batch-prefix.click](batch-prefix.click) proves the native transition, positivity,
checked iterator endpoints and coupling of the deferred state to the global
checksum prefix. Its zero-lane residue lemma initializes B from any canonical
entry value. The original inner back edge, scalar seed addition, reductions and
outer back edge retain the common B specification. It introduces no processed
counter. The remainder reuses these native transition and positivity lemmas.
Its original scalar seed addition, reductions and recombination now preserve
those residues. The original scalar tail carries both scalar residues against the global
`length - remaining` prefix. Its full-range byte bridge identifies the actual
post-`Next` byte at `length - remaining - 1`. B uses the newly updated A value.
Actual exhaustion establishes the complete-input residues; byte extensionality
transports them to the entry snapshot, and checked final reductions and 16-bit
stores establish both receiver-field postconditions. The native byte bridge
verifies, expands and reverifies; false final A and B specifications are rejected.

The harness assembles the contract with the checked helper/getter bodies,
iterator and recombination libraries, general partition lemmas, and tail
bounds. Normal tests check the bounded metadata and native stored-guard
regression. Nightly tests check the complete body, missing authority and seeds,
false final bounds, absolute lane values, a duplicated A-transition byte, and
a false lane-reduction residue, an incorrect deferred B seed product and a false
B reduction residue, a changed entry B seed and a full-input claim at the
completed-batch boundary, a duplicated remainder A byte and a changed remainder
B seed, false scalar A and B recombination observations, plus CLI
verify/profile/audit/expanded-proof agreement.
The deferred B lemmas independently verify, profile, audit, expand and reverify;
mutations reject incorrect native positions, byte weights, missing overflow
bounds, invalid reduction floors, wrong global-prefix advances and changed seeds. The absolute-position lemmas also
expand and reverify independently; mutations reject undefined pointer sums and
false byte observations.

```sh
cargo nextest run --profile nightly --test rust_import \
  -E 'test(charon_adler2_general_compute)'
```

The whole-body bounds and termination proof includes both A and B correctness
for the full-batch prefix. Complete checksum and incremental processing postconditions
remain separate roadmap work.
