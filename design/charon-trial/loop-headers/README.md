# Split while headers

`loops.rs` and `sum.rs` are byte-for-byte copies of the `rust-loops` and
`rust-byte-sum` sources; `loops.click` and `sum.click` archive their original
sidecars, respelled once in today's syntax (`../README.md`, Complete canonical proof-port adoption). Both now import through Charon. The frozen
sidecars retain their numeric-frontier failures: respectively “requires the
execution frontier to be at a loop” and “local `i` has no value at this frontier”.
They remain proof gaps in the parity inventory.

`loops-proof.click` changes only three entry selectors to `loop(0)`. Its three
contracts verify the unchanged count, accumulate, and byte-walk bodies.
`headers.rs` additionally proves an assignment performed on the final false
header test and a negated shared-slice-length comparison. False result claims
fail; verification, profiling, auditing, and expanded certificates agree.
These adapted/synthetic proofs do not increase frozen fixture parity.

The adapter recognizes a linear, single-entry chain from the natural header to
its conditional test. It reconstructs the guard in statement order using
bounded pure scalar substitution and shared-slice metadata, then emits the
original header statements on every test, including the final false test.
It preserves actual local state and emits no processed-count variable or
manufactured break. Single-block headers retain their existing structure.

Guard substitution is limited to 256 expression nodes. Ordinary calls, memory
reads, arithmetic, mutable/reference borrows, shared header entries, and extra
exits remain rejected. Scaling regressions at 8, 32, and 128 header blocks check
linear charged work and emitted statement counts; nested-loop regressions
remain covered. Live extraction also checks these rejected source shapes and
retains the complete frozen parity sweep.

`split-shared-slice-while-header-v1` versions this semantic expansion. Previous
ULLBC artifacts, compiler pins, and extraction flags are unchanged; locks are
updated deliberately. External Charon locks require an explicit refresh.

```sh
scripts/check.sh --charon-live
cargo nextest run --lib --test rust_import -E 'test(charon_loop_headers_) | test(split_while_) | test(mir_while_) | test(nested_while_)'
```

Current fixture parity is 10/16 (62.5%); import coverage is 14/16 (87.5%). Next
resolve stable proof observations for numeric frontiers and iterator state,
plus the remaining owned-iterator and tuple/slice-return normalization gaps,
before switching the default and retiring legacy extraction.

## Named assignment frontiers

`loops-assignments.click` additionally selects `assignment(i, 0)` and checks
that the first real store initializes `i` to zero, before selecting the loop.
All three unchanged Rust loop bodies verify; false initialization claims fail.
The shared proof layout indexes ordinary local assignments, local compound updates, and call-result
assignments by local name and zero-based static occurrence. Unrelated locals
and stores do not shift these targets. Every crossed transition and the selected
store still need checked execution; branches and backward/unreachable targets
are not bypassed. The selector stops before the store itself, which may follow
compiler-generated right-hand-side helpers. `loop(N)` selects the loop entry;
`mark` names a reached state. Assignment selectors are not state expressions.

Both syntax and typed-kernel layouts index these targets once, with immutable
sharing and deterministic scaling at 8, 128, and 1024 store pairs. Live Charon
re-extraction verifies the same proof after inserting an unrelated compiler
local in an isolated probe. Verification, profiling, auditing, and expanded
certificates agree. Frozen sources are unchanged and the original sidecars keep their contracts and proofs; parity
remains 10/16 and imports 14/16. Numeric-selector compatibility and stable
iterator observations remain migration work.

## Byte-sum proof frontiers

`sum-proof.click` verifies the unchanged `rust-byte-sum` body and original
prefix-sum contract. It selects `loop(0)` for initialization, `read(0)` before
the actual byte load, and `assignment(i, 1)` before the index update. Checked
steps establish the byte bounds and overflow obligations; three final steps
execute the remaining real header cleanup before returning to the backedge.
No compiler temporary name or generated processed count appears in the proof.
Verification, profiling, auditing, expansion and expanded rechecking cover
this complete proof, including a false result claim.

The parity inventory separately records migrated proof sidecars. Together with
the ten frozen successes, these prove the original sources and contracts of
12/16 fixtures (75%). AST comparisons protect the original contracts and pure
specification functions; the live gate checks both migrated sidecars after
fresh extraction. Frozen-sidecar parity remains 10/16 (62.5%), and import
coverage remains 14/16 (87.5%). These are distinct measures, not Rust-language
coverage. Remaining work includes iterator observations, owned iterator and
tuple/slice-return normalization, and frozen selector compatibility before
the default changes.
