# Shared object-model recovery audit: 2026-10-14

## Revisions and reproducibility

This is a fixed-baseline audit, not a green verdict for the accumulated model.

| Item | Revision or identity |
| --- | --- |
| Master baseline | `325f9f604` (immutable during this comparison) |
| Archived implementation | `b92deef95`; archive plus recovery plan `e3d84a785` |
| Preserved fork branch | [`codex/object-model-archive-2026-10-14`](https://github.com/lacker/click/tree/codex/object-model-archive-2026-10-14), pointing at `e3d84a785` |
| Published #646 at audit start | Open; `lacker:codex/initialized-byte-output` at `4d86a66e72e9a02f9f51107c77a268c7b08b4d57`; no auto-merge request or queue entry |
| Master worktree | `/workspace/click-object-audit`, `codex/object-model-baseline-audit` |
| First extraction worktree | `/workspace/click-object-pointer-values`; initially `325f9f604`, rebased to `2010b27f1` for delivery |
| Verifier toolchain | rustc/cargo 1.98.1; mdBook 0.4.52; LLVM/Clang 19.1.7 |
| Rust import compiler | `nightly-2026-09-17`, commit `923c95cdf5ba65cea505aa2ea829f578e1506ed8` |
| Charon extractor pin | `5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` |
| Cargo.lock SHA-256 | `8ddfd94c170a27378392f305f6904f0114d9cf772e0624f38b19654d25833652` |
| Charon profile SHA-256 | `fe1d73e76ebabdf5d32230a27164dd2845782d05a395da8b649270ff3e2ccb1c` |
| Exporter schemas | Master 59; archive 60; each run uses its own revision's exporter |
| Master exporter SHA-256 | `8c4ee9ff0fe110603d18ff62c6b836ca34b4ba75b7fbb72bc2ce0ce1884c1f91` |
| Archive exporter SHA-256 | `d4ac8f2a4350400ab0a63a22f03126f5f525273f8bda6f16de02b0b011c4e29d` |

Latest remote master at audit start was `943b72c759cfa139585475a77d8de04ea857d569`.
The comparison deliberately stays on the master revision already integrated in
the archive; a later delivery must account for newer upstream changes separately.

All `examples/` C, C++, Rust and Click program/contract files are identical
between baseline and archive. The only tracked example-tree difference is
`marked-linked-list/README.md`. Both runs exercise the 52 normal projects;
the two existing nightly rbtree projects remain excluded. The archive harness
additionally implements the approved numeric-only marked-list rejection and
constructor-positive controls; those expectations are not treated as regressions.

## Commands and observed results

Baseline example comparison:

```sh
source /workspace/.click-tools/activate.sh
export CARGO_TARGET_DIR=/workspace/click-cpp-bytes/target
export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER=/workspace/click-object-audit/target/cpp-exporter/click-cpp-exporter
cargo test --test examples example_projects -- --exact --nocapture
```

Result: **52/52 pass**, exit 0, 107.31 seconds for the harness. The baseline
was unmodified. `scripts/check.sh --ci-quality` also passes: formatting,
environment setup regressions, all-target Clippy, book build and structural
documentation lint. Vale is absent and its advisory prose lint is skipped.

The archive's latest compiled example executable was preserved before changing
Cargo revisions, then run with the archive exporter and the same exact test:

```sh
export RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER=/workspace/click-object-design/target/cpp-exporter/click-cpp-exporter
/tmp/object-model-archive-examples --exact example_projects --nocapture
```

Result: **35/52 pass, 17 fail**, exit 101, 79.66 seconds. This reproduces the
prior archive result rather than comparing against an old log alone. The
executable SHA-256 is
`865e49098945a78e4810f83bb5d02827385a5e1dc696a7b5509f7fc99cf6b1c2`.
Its compiled manifest points to the archived worktree. Neither timing is a
performance claim; concurrent compilation and different search paths affect it.

### Normal-gate provenance

The initial baseline `scripts/check.sh` run exits 0, but it is **not a valid full
baseline verdict**. Its unit/import/CLI stage passes all 5,577 selected tests
(1,486 skipped). Concurrent extraction compilation subsequently replaces the
shared target directory's fixture binaries: those fixture logs identify
`/workspace/click-object-pointer-values`, rather than the baseline checkout.
A sequential fixture retry also reuses those artifacts and is interrupted.
Neither fixture result is credited to master.

Before the replacement run, stop competing Cargo builds and remove only Click's
package artifacts, preserving dependency caches:

```sh
# In /workspace/click-object-audit, with the environment above.
cargo clean -p clicklang
scripts/check.sh
```

The rebuilt baseline normal gate **passes, exit 0**: 5,577 selected unit,
import and CLI tests pass (1,486 skipped), all 52 normal example projects pass,
and the normal Markdown corpus passes. All fixture paths identify the baseline
checkout. The unit stage takes 191.305 seconds, examples 122.50 seconds and
Markdown fixtures 104.67 seconds. The total is 20m17s and emits the ten-minute
budget warning: the cold test compilation alone takes 9m09s, with another
3m39s for Clippy. This is a correct functional verdict, not an under-budget
run or a verifier performance claim. No limits or test selection are changed.
The archive's full normal gate remains unestablished; its example stage fails.

Check the compiled
manifest/fixture paths as well as the command's exit status. Never share
mutable Click artifacts between concurrent worktree builds when comparing
revisions. Prefer a separate `CARGO_TARGET_DIR` per concurrently built worktree;
when reusing a directory sequentially, remove the package's artifacts on a
revision switch and inspect the resulting paths. The independent baseline and archive example executables used in
the comparison above were tied to their correct checkout before switching
builds; their recorded 52-versus-35 result remains valid.

## Checked failure ledger

Every row below passes on fixed master and fails on the archive with the
unchanged source and claims. Classification is **branch verification regression**;
introducing commit and semantic cause remain unassigned. Similar errors suggest
reduction groups, not proven shared causes. Engineering owner is the shared
object-model recovery workstream. This records changed verification behavior,
not a conclusion that every previously accepted contract is sufficient under
the sound pointer laws. A demonstrated necessary semantic narrowing must be
recorded separately, with source-language evidence and explicit compatibility
accounting; baseline acceptance alone cannot establish that judgment.

| Project | Selected failure on archive | Required follow-up |
| --- | --- | --- |
| [allocated-linked-list](../examples/allocated-linked-list/allocated_linked_list.click) | `list_pipeline`: native composite body guard not established | Reduce and attribute; preserve original positive, expansion and retained checks |
| [arena](../examples/arena/arena_cells.click) | `arena_alloc.loop(1).preserve`: authority unavailable for `arena->data` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [binary-tree](../examples/binary-tree/binary_tree.click) | observed child resource: missing `defined(old(*pointer))` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [concurrency-fork-join](../examples/concurrency-fork-join/fork_join.click) | `fill_range` loop condition: required resource unavailable | Reduce and attribute; preserve original positive, expansion and retained checks |
| [detachable-buffer](../examples/detachable-buffer/detachable_buffer.click) | call transfer: native span lacks exact unresolved/loaded identity | Reduce and attribute; preserve original positive, expansion and retained checks |
| [heap-object](../examples/heap-object/heap_object.click) | `item_pipeline`: native composite body guard not established | Reduce and attribute; preserve original positive, expansion and retained checks |
| [input-cursor](../examples/input-cursor/input_cursor.click) | produced borrowing composite has no backing viewed call input | Reduce and attribute; preserve original positive, expansion and retained checks |
| [multifile-registry](../examples/multifile-registry/registry.click) | `registry_run`: invalid memory access | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-segmented-buffer](../examples/owned-segmented-buffer/owned_segmented_buffer.click) | call transfer: native span lacks exact unresolved/loaded identity | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-split-buffer](../examples/owned-split-buffer/owned_split_buffer.click) | call transfer: native span lacks exact unresolved/loaded identity | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-string](../examples/owned-string/owned_string.click) | stored-element postcondition unavailable to `assumption` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-vector](../examples/owned-vector/vector.click) | stored-element and pointer-field frame postconditions unavailable | Reduce and attribute; preserve original positive, expansion and retained checks |
| [rbtree-augmented](../examples/rbtree-augmented/rbtree_erase_leaf.click) | `rb_erase_augmented`: `simp` did not retain a complete ensure proof | Reduce and attribute; preserve original positive, expansion and retained checks |
| [refcount](../examples/refcount/refcount.click) | `refcount_pipeline`: `auto` cannot prove `amount < obj->refs` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [ring-buffer](../examples/ring-buffer/ring_buffer.click) | `ring_buffer_pipeline`: `normalize` does not establish the goal | Reduce and attribute; preserve original positive, expansion and retained checks |
| [rust-byte-sum](../examples/rust-byte-sum/sum.click) | deterministic smart-work budget exhausted at statement 63 | Reduce the work curve; retain the existing budget and original proof claim |
| [rust-chunks-exact](../examples/rust-chunks-exact/chunks.click) | loop preservation: pointer arithmetic leaves pointed-to object | Reduce and attribute; preserve original positive, expansion and retained checks |

The [existing pointer-field frame bug](../bugs/c-pointer-field-postconditions-lose-frame-evidence.md)
tracks the vector/string group. Other groups need reductions before filing new
bugs or choosing semantic changes. In particular, rbtree-augmented and refcount
are not master failures at this revision; the earlier unclassified report left
that question open.

## Independent defect and extraction candidate

Master rejects a resource owning `p[0]` when its pointer argument is substituted
with a complete captured value. It reports `a pointer operation has no known
pointee type`. The archive accepts the same small C program:

```c
int32 probe(int32* p, int32 input) {
    p[0] = input;
    return input;
}
```

```click
resource cell(p: int32*) { owns p[0]; }
int32 probe(int32* p, int32 input) {
    owns cell(p);
    ensures result == input;
} by { unfold(cell(p)); execute(); fold(cell(p)); simp(); }
```

The extraction adds only
`CExpression::Value(value) => value.c_type().pointee_type()` to the existing
pointee-type lookup. It requires no new pointer representation, profile,
initialization effect, importer schema or keyword. The existing complete value
supplies its type; access checks still decide storage authority and validity.
The positive and view-only write rejection are separate focused Markdown
regressions. The extracted patch is committed as `11d9f44b9` on the clean-baseline branch
`codex/object-model-pointer-values`, not cherry-picked with the surrounding
object-model activation. The same patch rebases cleanly onto current upstream
`2010b27f1` as `1b695539d`; delivery checks on that revision are separate from
the frozen baseline comparison. Its positive and view-only rejection both pass. The
positive also passes fresh verification, expansion, rewritten verification and
retained rechecking. All-target Clippy passes. The normal example run passes
51 projects and fails only because that worktree lacks its local C++ exporter;
after building that exporter, the focused `basic-cpp` rerun passes. These checks
cover all 52 projects but are not a single full green-tree run.

Alignment-result typing is **not** an independent candidate at this baseline:
`PointerAligned` itself belongs to the accumulated branch. Entry-argument folding
also needs a separate dependency/reproduction audit. Those are not bundled into
the first extraction merely because they shared a historical commit.

## P1 soundness recheck

The ordinary C reproduction in
[the scalar-subobject bug](../bugs/pointer-arithmetic-crosses-scalar-subobject.md)
still verifies incorrectly on both `325f9f604` and `e3d84a785`:

```c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) { return *(&p->first + 1); }
```

The sidecar is:

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

Both probes exit 0. Under C11's one-element scalar domain,
one-past `first` cannot be dereferenced to read `second`. The defect is still P1;
passing native/C++ controls must not be advertised as closing ordinary C.
The small typing extraction does not fix this soundness gap and must not claim
object-model completion. Its required repair needs the dependency closure of
source pointer production, designation transport and checked access, or an
explicit sound refusal that preserves legitimate source patterns.

## Change inventory and dependency boundaries

The comparison `git diff --numstat 325f9f604..e3d84a785` includes the recovery
plan commit, so it has 250 changed paths rather than the implementation
checkpoint's 249.

| Area | Changed paths | Added lines | Removed lines |
| --- | ---: | ---: | ---: |
| Design, documentation and backlog | 27 | 2498 | 41 |
| Other tools/integration metadata | 5 | 297 | 31 |
| Tests and proof fixtures | 23 | 1911 | 93 |
| CLI and audits | 4 | 69 | 45 |
| Shared kernel | 98 | 43280 | 1926 |
| C adapter | 4 | 1838 | 320 |
| C++ adapter | 11 | 2014 | 75 |
| Rust adapter | 4 | 345 | 36 |
| Contracts, proof, diagnostics and surface | 74 | 10748 | 3342 |

This is a responsibility inventory, not permission to split by directory:

1. **Independent type observation fix:** the captured-value case above; no
   activation dependency. Prepare the first green delivery with paired checks.
2. **Initialization/construction/representation:** shared initialization ranges,
   destination binding, completion, copies, lifetime events and the uint32 byte
   bridge touch execution and modular summaries. Identify already landed pieces
   before extracting remaining operations and their complete proof checks.
3. **Pointer model:** domains, full-value equality, pointer-valued cells and
   pointer/integer transport have coupled producers and consumers. No half-model
   that stores designation but loses it through substitution or calls can be
   called sound. Ordinary C's reproduced failure remains part of that closure.
4. **Native entry/call/resource activation:** the new `native_record_inputs`,
   `native_span_inputs`, pointer-result effects and contract lowering rely on
   those pointer laws. The 17 compatibility failures must be attributed here or
   elsewhere before enabling the affected profile in an extracted delivery.
5. **Frontends and pinned models:** C++ schema/library changes require matching
   importer validation, kernel support and profile-specific controls. C/Rust
   adapter changes cannot be pulled in as incidental fixes without their
   unchanged-source comparison and own admission evidence.
6. **Proof tools and audits:** source synthesis, snapshots, retained replay and
   instrumentation must agree with the selected semantic slice. Extract
   standalone defects where reproduced on master; keep semantic identity and
   certificate compatibility changes with their corresponding kernel change.

First code introduction for several pointer/entry modules is checkpoint
`55238f40b` (a WIP integration commit), followed by multiple repairs and merges.
That commit is a starting point for attribution, not a proposed delivery unit.
A new bisect must preserve original source/profile and avoid reporting build
failures as proof regressions.

## Completion ledger

- [x] Archive published to the fork; original PR state and immutable comparison
  revisions recorded; primary checkout and baseline source left untouched.
- [x] Compare all normal example projects with identical source/contract files.
- [x] Record all 17 branch failures and one independent master defect.
- [x] Recheck the ordinary C scalar-subobject P1 reproduction on both revisions.
- [x] Record a responsibility inventory and conservative dependency boundaries.
- [x] Establish the fixed master's normal-gate result with correct artifacts.
- [ ] Establish the archived candidate's full normal-gate result; its example
  stage is already a reproduced failure.
- [ ] Attribute the introducing changes for the 17 failures with reductions or
  bisect; choose the minimal sound pointer-activation closure.
- [ ] Complete and publish the first isolated green extraction; settle #646's
  replacement only after that result is concrete and the archive is linked.

Command logs for this session are in `/tmp/object-model-*.log`; commands,
revisions, error summaries and the small reproductions above remain committed
so the audit does not depend on those transient files.
