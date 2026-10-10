# Rust roadmap resume notes

This is a workspace-recovery handoff, not a completed proof or a replacement
for `issues/rust-support.md`. It preserves the useful investigation from the
workspace that disappeared during a cloud restart. The original temporary
proofs, logs, and uncommitted reference edits are unavailable. Reproduce the
observations below on current upstream before changing semantics.

## Authorization and delivery

The user authorized completing the remaining Rust roadmap, delivering sizable
increments through fork PRs, and auto-merge through the normal checked queue.
Continue until a material design decision needs their input. Do not ask again
for routine implementation or delivery permission. No subagents are authorized.
Keep the roadmap a current status document rather than a historical log.
Keep the selected original Rust and C implementation bytes unchanged.

## Saved implementation

The following changes are already merged upstream:

- PR 591: consumed values and sequencing of C prefix/postfix expression
  updates, original zlib import, and the empty-input contract.
- PR 594: numeric induction retains its required definedness guards; the
  common Adler specification proves concatenation and incremental A/B/packed
  checksum equality. This does not establish implementation correctness.
- PR 597: bounded byte/word Integer conversion, checked unsigned 16-bit field
  packing, and unchanged zlib one-byte checksum and null-reset proofs.

The last implementation baseline used by this investigation was
`0ee8a67357c9514c40cc0015e79bdff8e5d8aef0` (PR 597). The final implementation
commit was `28ea758660889dcde12eecf9d01b70e8b1aa5eb3`; its inclusion upstream was
verified. Its full Nextest library run passed 5,255 tests with 136 skipped.
Subsequent upstream changes must be assessed before reproducing these cases.

Canonical starting points:

- `issues/rust-support.md`
- `design/rust-checksum-assessment.md`
- `design/adler32-spec.click`
- `design/charon-trial/adler2/README.md` and its whole-body bounds sidecars
- `design/charon-trial/zlib/README.md`
- `docs/reference/rust.md`

Remaining deliverables are arbitrary-length Rust A/B and packed checksum
correctness, implementation incremental correctness, general unchanged zlib
correctness and C/Rust equality, production exclusive-child suspension/recovery,
stable source-facing proof observations, and the model/composition/documentation
acceptance criteria in the roadmap. Charon extraction migration itself is done.

## Lost functional-proof prototype

The prototype assembled the existing helpers, partition facts, and whole-body
numeric bounds proof into one prepared Rust verification unit. It retained
actual cursor/remaining metadata and shared input views, without a generated
processed count. Its final contract still stated bounds, not functional A/B
correctness.

The working A relation was that `a + sum(a_vec[0..4])` is congruent modulo 65,521
to the common specification's A value on the already consumed input prefix.
The previous session reported a verified first full-batch A checkpoint, including
the four-byte updates and lane reductions. The script and certificate are lost:
reconstruct and verify this checkpoint rather than treating this note as proof.
The remainder-vector loop was the active unfinished step; B was not connected.

For the remainder loop, the signed consumed prefix was the signed observation
of `F` minus the signed observation of actual remaining metadata, where
`F = bytes_len - bytes_len % 4`. The loop-head snapshot gives the previous prefix;
after the native decrement by four, prove the new prefix equals the old prefix
plus four. Explicitly prove the subtraction/addition definedness and the input
window bounds before using four-byte specification recurrences.

Useful generic helper shapes were checked separately:

- Bounded native unsigned difference agrees with the difference of bounded
  signed observations.
- If `4 <= remaining <= total <= n <= i32::MAX` and the counts are nonnegative,
  the consumed prefix is defined, nonnegative, at most `i32::MAX - 4`, and its
  successor by four is defined and at most `n`.
- Under those explicit domains, decrementing remaining by four increments
  consumed prefix by four.
- `defined(q + 4)` and `q + 4 <= n` imply `q < n`.

The optimized B representative is
`b + 4 * sum(b_vec) - a_vec[1] - 2*a_vec[2] - 3*a_vec[3]`.
It can be negative after independent lane reductions. Do not silently apply
lemmas requiring a nonnegative representative; supply the correct quotient or
an explicitly justified equivalent representative.

## Active observation and shared-view investigations

At the remainder constructor call in the pinned artifact, the returned vector
was local `__rust_mir_68`, and its shared byte pointer was `__rust_mir_69`.
In the first full-batch loop the corresponding locals were 42 and 43. These IDs
are artifact-specific. The constructor is the qualified U32X4 `From` body;
its canonical verified contract exports mathematical entry-byte values.

In a reduced four-byte computation proof, native equality between returned
lane zero and the pointer's byte zero passed. A helper equating the mathematical
observations of two equal `int32` arguments applied successfully, but a following
exact `assumption` for those observations failed. Direct unrestricted `simp`
also failed and could become expensive. This is an investigation frontier,
not an established diagnosis or justification to broaden the kernel.

Smaller straight-line controls passed:

- C copying a byte into a scalar field, and into a four-word array field.
- C returning a record containing four promoted bytes, then observing its
  first lane in the caller.
- Equivalent Rust record construction and return, using a schema-4 crate
  import and the qualified identities for crate `word`.

The Rust control source had `Word([u32; 4])`, a `make(&[u8]) -> Word` constructor
promoting the first four bytes, and a caller returning its first lane. With
`bytes_len == 4`, input views, a constructor native-byte postcondition, and
an `equal_i32_math` theorem, native cast equality and the subsequent exact
Integer equality both verified. Therefore returned arrays alone did not
reproduce the failure.

A variant accumulated that lane inside `bytes.chunks_exact(4)`. A loop proof
with original input views, `iter_size == 4`, remaining bounded by four and
divisible by four, and a cursor/prefix relation reached the constructor but
reported missing stable-view backing/binding. A final revision recorded the
loop head, established head remaining equal to four and the yielded pointer
equal to the input, then stepped the call. Its result was not recovered before
the workspace died. Re-run it before calling this a resource defect; inadequate
range or authority evidence remains a possible explanation.

The larger prototype also reported that adding a signed pointer bridge before
the constructor led to an invalid stable-view evidence refusal, while moving
that observation after the constructor passed the call. Reduce this apparent
sensitivity rather than keeping arbitrary proof-order workarounds.

### Code-reading leads, not confirmed fixes

At the investigation baseline:

- `src/kernel/assumptions.rs::conditions_equal_with_load_atoms` handled native
  comparisons but not Integer comparisons.
- `src/kernel/proof/fact_keys.rs::snapshot_blind_proposition_key_one` retained
  exact keys for Integer comparisons, including their snapshot identities.
- `src/kernel/proof/facts.rs::with_selected_load_equality_bridge` materialized
  selected native word/pointer equalities, not Integer observation equalities.
- `src/surface/proof/theorem_application.rs` captured machine arguments before
  lowering a theorem's clauses; deferred `to_integer` reads follow a different
  lowering route in `src/surface/lowering/annotations.rs` and `src/kernel/spec.rs`.

A candidate to investigate is a narrowly checked, goal-directed congruence rule
for two observations of the same machine format, derived from the corresponding
checked native equality. Require real unchanged-memory/frame evidence where
needed. Do not erase snapshots, equate signed/unsigned formats without bounds,
scan unrelated ambient facts, or assume this fixes the reduced case.
Retain changed-byte, mismatched-format, absent-evidence, and scaling negatives.

The stable-view missing-binding check is in `src/kernel/loans.rs` near the
call transfer planner. It distinguishes resource view occurrences from the
ledger bindings that give them authority. Inspect loop invariant resource
transitions and pointer-equivalent view occurrence selection if the reduction
still fails after supplying the required bounds.

## Reference corrections to reconstruct

The lost uncommitted edit removed obsolete descriptions of artifact `SliceFor`
nodes and `__rust_iter_LINE_COLUMN` names from `docs/reference/rust.md`.
Native Charon retains iterator construction, next calls, and Option branches in
ULLBC; the adapter validates the protocol and lowers actual iterator state.
Unique source local names survive; ambiguous or unnamed locals use
collision-checked `__rust_mir_ID` names with component suffixes. These are not
yet stable source-facing observations. Internal adapter `IntegerFrom` operations
must not be described as Charon artifact nodes. The blanket statement excluding
array iteration was also stale: the canonical shared scalar array iteration
trial already exists. Check current evidence before revising other exclusions.

## Practical verification details

Use the restored `/workspace/.click-tools/activate.sh` if available. Previous
builds used one Cargo job, disabled Cargo incremental compilation, and
`RUST_MIN_STACK=8388608`. Set `CLICK_CHARON` and `CLICK_CPP_EXPORTER` to the
executables built in the task worktree. The C++ exporter must match current
source; schema identity alone does not establish that it is current.

Prefer process-isolated Nextest for the full library run. The previous builtin
parallel test run had a budget-instrumentation interaction that passed alone
and in the full Nextest run; avoid treating that as a checksum defect.
Select the intended Rust contract by its current declaration line and verify
the reported selected-proof count; a stale selector can verify zero proofs.
Rust `--trace-proof` was unsupported at the baseline. Prepared import sidecar
expansion required the same filename; back up outside the repository first.
Keep slow full proof, expansion, and mutation checks nightly.

Do not restore missing files from an unrelated primary checkout, rewrite the
original checksum implementation, increase tactic budgets, or claim these
notes are a passing proof artifact. Rebuild bounded reductions and save the
next verified checkpoint promptly.
