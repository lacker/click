# Charon extraction assessment for Click

## Completed Linux frontend delivery

The Rust P1 frontend milestone is complete. By maintainer decision on 2026-10-15,
its launch host scope is Linux x86-64 GNU (`x86_64-unknown-linux-gnu`). A second
host platform is optional and is not a launch requirement. That scope was
superseded on 2026-11-10: further hosts and crates with third-party
dependencies are launch work in
[the Rust support roadmap item](../roadmap/rust-support.md). Rust continues to
cover the experimental subset in the [reference](../docs/reference/rust.md)
and [coverage matrix](../docs/reference/coverage.md).

The installed pipeline ships pinned Charon, its paired driver and rustc runtime;
uses explicit versioned resolution and identity checks; emits portable schema-9
release/profile lock identities; and names crate-closure and frontend recovery
errors. Legacy identities remain readable offline. The real release-archive
regression relocates installation and demonstration, reproduces the committed
basic/adler2 locks, then verifies all 881 C/Rust demonstration proofs with an
empty PATH and the frontend removed. The [installed instructions](../examples/basic-rust/README.md)
and [checksum demonstration](adler32/project/checksum-correspondence.md#reproduce)
record the supported workflow and its original-source, signed-length and
matched-input boundaries.

Delivery landed in [#1086](https://github.com/clicklang/click/pull/1086),
[#1095](https://github.com/clicklang/click/pull/1095),
[#1109](https://github.com/clicklang/click/pull/1109),
[#1118](https://github.com/clicklang/click/pull/1118) and
[#1134](https://github.com/clicklang/click/pull/1134). The completed P1 roadmap
entry has been removed. Additional hosts and broader language coverage are
optional future work; shared project configuration is described under
[Project units](../docs/reference/cli/import.md#project-units).

The compiler investigation below is historical evidence. Current production
borrow authority is recorded in its [assessment](rust-borrow-authority-assessment.md),
resource laws in [Rust resource correspondence](rust-resource-correspondence.md),
and the construction/return contract in [aggregate construction](aggregate-construction.md).
Existing post-launch context is retained at the end of this assessment.

## Historical extraction assessment

Assessed on 2026-10-02. This is extraction evidence and an adoption proposal,
not a new supported frontend or a checksum verification result.

Follow-up: the [end-to-end adapter trial](charon-trial/README.md) connects the
candidate to Click's existing checker for arithmetic and owned guard cleanup.
It records a deliberately different MIR/transform selection and its trust
boundary; the extraction measurements below retain their original configuration.

## Recommendation

Charon is a credible foundation for Click's Rust extractor. A bounded live
probe extracted both the composition case that motivates consolidation and
the unchanged, pinned adler2 checksum path. Prefer a small end-to-end adapter
experiment over adding more independent HIR and MIR feature paths. Use
Charon's **ULLBC** (unstructured basic-block representation) as the candidate
semantic input, with a Click-owned representation and the existing checked
engine downstream. Preserve source metadata for sidecars and diagnostics.

This reuses compiler integration, resolved types/calls, places, checks, and
drop extraction. It does not supply Click contracts, library interpretations,
memory authority, loop invariants, or proof certificates. Aeneas's functional
interpretation of LLBC is a separate backend design; adopting Charon does not
require adopting that interpretation or replacing Click's memory model.

## HIR, THIR, MIR, and Verus

The useful simplified pipeline is HIR -> THIR -> MIR. HIR retains more source
structure; THIR follows type checking and makes adjustments such as
autoref/autoderef and resolved overloaded calls explicit. MIR makes evaluation,
moves, control flow, and cleanup explicit, with additional transformations at
successive MIR phases. Source structure is lost while useful semantic facts
are made explicit. HIR alone is not a complete substitute for type-checking
results, ownership analysis, or drop elaboration.

Click could implement some lowering itself. Every such operation then needs
faithful evaluation order, adjustments, moves, temporary lifetimes, and cleanup
semantics. Reimplementing the difficult part of rustc's lowering increases the
translator trust and maintenance burden. A source-facing HIR/THIR layer remains
useful, but it should annotate a single semantic body rather than introduce a
second meaning for Rust operations depending on whether a guard is present.

Verus has access to these compiler stages. Its architecture is commonly
summarized as HIR -> VIR -> SST -> AIR, but its driver explicitly describes
**HIR/THIR -> VIR** for verification and **HIR/THIR -> MIR** for executable
Rust, plus compiler lifetime checking and synthetic checks for ghost code.
There is no fundamental MIR-access limitation motivating its choice of VIR.
The choice reflects its proof language and interpretation. Borrow the separation
between compiler integration, semantic representation, and proof backend;
which execution/resource semantics Click supports still needs its own decision.

Sources: [rustc THIR guide](https://github.com/rust-lang/rustc-dev-guide/blob/master/src/thir.md),
[MIR guide](https://github.com/rust-lang/rustc-dev-guide/blob/master/src/mir/index.md),
[Verus architecture](https://github.com/verus-lang/verus/blob/main/source/CODE.md),
and [Verus driver](https://github.com/verus-lang/verus/blob/main/source/rust_verify/src/driver.rs).
The Verus links describe the inspected upstream architecture and are not an
input dependency of Click.

## Pinned extraction experiment

| Input | Selection |
| --- | --- |
| Charon | `0.1.279`, revision `5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` |
| rustc | `nightly-2026-09-17`, commit `923c95cdf5ba65cea505aa2ea829f578e1506ed8` |
| Target | `x86_64-unknown-linux-gnu` |
| Semantics | overflow checks on, panic abort, MIR opt level 0 |
| Extraction | ULLBC, elaborated MIR, precise drops, default installed sysroot |
| External library bodies | `core`, `alloc`, and `std` opaque |

No Charon preset was used. Borrow checking and type checking remained enabled.
Fallible-operation reconstruction, indexing-to-calls, and operations-to-calls
remained disabled, keeping explicit assertions and compact array operations.
The reproducer rejects failed or partial artifacts (`has_errors`). A separate
LLBC extraction of the composition source also succeeded; its reconstruction
scaling was not measured.

The composition source combines a restoring `Drop` guard, a mutable borrow,
`u16` arithmetic and `u32::from`, arrays, stored `chunks_exact` and its remainder,
shared byte iteration, indexed updates, an early return, a move, and explicit
drop. Companion functions expose overflow, bounds, division-by-zero, and shift
checks. A tuple-struct array with custom `AddAssign` tests resolved operators.

| Probe | Observed result |
| --- | --- |
| Composition `combined` | 60 blocks, 190 statements, 12 explicit assertions, one precise implicit drop, and the explicit `mem::drop` call |
| Arithmetic companions | One explicit assertion each for increment, indexing, division, and shift |
| Conflicting borrow | rustc E0506; nonzero exit and no extraction artifact |
| Use after move | rustc E0382; nonzero exit and no extraction artifact |
| Unchanged adler2 `adler32_slice` root | 15 translated bodies including generated glue; `compute` has 150 blocks |

The adler2 `lib.rs` and `algo.rs` bytes match
[the existing source manifest](rust-checksum-sources.json), revision
`89a031a0f42eeff31c70dc598b398cbf31f1680f`. Extraction used edition 2021 and the
`std` feature, preserving its tuple structs, custom operators, indexed updates,
and optimized loops. **The compiler differs from the manifest's June pin.**
This establishes compatibility with the inspected Charon/compiler pair, not
compatibility with the current production profile or verification of Adler-32.
Opaque library bodies require named interpretations or separately verified code.

Compactness and control-flow probes measured representation growth:

| Repeat length | Artifact bytes | Blocks | Statements |
| --- | ---: | ---: | ---: |
| 16 | 47,505 | 3 | 10 |
| 4,096 | 47,515 | 3 | 10 |
| 1,000,000 | 47,530 | 3 | 10 |

| Sequential branch diamonds | Blocks | Statements |
| --- | ---: | ---: |
| 8 | 57 | 74 |
| 32 | 225 | 290 |
| 128 | 897 | 1,154 |

The repeat retains one compact operation, and branch joins remain shared
(`7N + 1` blocks, `9N + 2` statements). These are extraction measurements,
not claims about Click checking time. Whole-array copy growth and unrelated
proof-context growth still need adapter/kernel regressions.

## Conditions for adoption

1. **Compiler and extraction identity.** This Charon pin needs a newer compiler
   than Click's exporter. Evaluate a coordinated profile update or an older
   compatible Charon revision; do not silently change the existing source lock.
   Bind the full extractor revision/binary, compiler, options, target/layout,
   modules, dependencies, and library models in prepared inputs. Charon's
   artifact version alone is insufficient. Use its typed library/schema for a
   production adapter rather than the probe's minimal JSON field inspection.
2. **Actual MIR phase provenance.** Charon's selected MIR phase can fall back
   to optimized MIR if an earlier body is unavailable; dependencies can only
   expose optimized MIR. The global option is not per-body provenance. Require
   explicit phase evidence or a justified policy for every accepted fallback.
   Reject partial artifacts and missing required bodies.
3. **Checked semantic mapping.** Preserve checks, typed places/projections,
   overflow modes, storage lifetime, move events, and resolved drop glue in one
   adapter. Maintain explicit panic obligations and Click's authority rules.
   Compiler-generated glue may use unsafe/raw operations even for safe source;
   distinguish that origin from admitting arbitrary unsafe Rust. An abort
   profile also needs a precise interpretation of unreachable unwind edges.
4. **Proof/source correspondence.** Item IDs, files, and spans are useful
   foundations, but MIR has lost source loop forms and some scopes. Define
   stable sidecar observations and loop/operation identities. Retain source
   metadata as needed without heuristic HIR/MIR matching or depending on
   temporary spelling. ULLBC keeps joins shared; avoid expanding paths while
   making control flow available to the existing engine.
5. **Library registry and resources.** Resolve supported instances by item and
   type arguments, with named contracts, effects, and panic behavior. Declared
   regions and reference types do not provide a body-level live-loan graph;
   Charon does not promise that information. Continue rustc borrow legality and
   checked Click permissions, and add compiler metadata if explicit loan
   recovery requires it. Compact extracted arrays still need compact shared
   kernel value/authority operations.

These conditions should be assessed against the pinned
[options](https://github.com/AeneasVerif/charon/blob/5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb/charon/src/options.rs),
[MIR selection](https://github.com/AeneasVerif/charon/blob/5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb/charon/src/bin/charon-driver/translate/get_mir.rs),
and [transforms](https://github.com/AeneasVerif/charon/tree/5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb/charon/src/transform).
Optional transforms can change which obligations are explicit; adopting an
Aeneas preset without auditing it is not the configuration tested here.

## Next bounded increment

Prototype a ULLBC adapter for a checked increment and an owned restoring guard
through the ordinary Click engine. Verify true postconditions; reject false
values, possible overflow, forged authority, and duplicate cleanup at their
documented boundaries. Exercise verification, profiling, audit, and expansion,
including checking the expanded proof. Then compose the guard with a borrowed
loop and add compact-array/control-flow scaling checks. Only promote the adapter
after those results and phase/source locks are reviewable. Successful extraction
of the checksum is a reason to run this experiment, not to skip it.

## Reproduction

Build the pinned external tool without changing Click's default compiler:

```bash
git clone https://github.com/AeneasVerif/charon.git /tmp/click-charon
git -C /tmp/click-charon checkout 5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev --component rust-src
charon_sysroot=$(rustc +nightly-2026-09-17 --print sysroot)
export LIBRARY_PATH="$charon_sysroot/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export CARGO_PROFILE_DEV_DEBUG=0
cargo +nightly-2026-09-17 build --locked --manifest-path /tmp/click-charon/charon/Cargo.toml --target-dir /tmp/click-charon-target --bin charon --bin charon-driver
python3 design/borrow-probes/charon_probe.py --charon /tmp/click-charon-target/debug/charon --output /tmp/click-charon-results
```

Use a fresh output directory. Each extractor invocation has a 45-second external
process containment bound; no invocation timed out in the recorded run. To
include the checksum probe, download the original `src/lib.rs` and `src/algo.rs`
at the manifest revision into one directory and pass `--adler2-dir DIRECTORY`.
The script checks both source hashes before extraction. Artifacts and logs are
external investigation outputs; the normal repository gate does not run Charon
or install this extra toolchain. No external tool source was patched for the
experiment.

## Existing post-launch context

The following context is preserved from the closed P1 roadmap. It records
existing limitations and evidence, rather than new roadmap commitments or
requirements for the Linux launch. The dedicated production assessments remain
the authority for their current implementation boundaries.


The checksum demonstration is complete for P1, and none of these items is
needed to finish a claim already made:

- **Wider checksum range.** Lengths beyond the shared signed specification
  range (2,147,483,647 bytes) remain unproved for both implementations; the
  current claims state that range explicitly.
- **Borrow authority.** Connect explicit exclusive-child suspension and
  recovery to production resource transitions. Compiler borrow rejection
  alone does not establish rejection of forged sidecar authority. The
  [production assessment](rust-borrow-authority-assessment.md)
  records what is delivered:
  - the synchronous borrowed-memory call protocol, with kernel negatives;
  - parent reuse after the child's last use;
  - the read-only import-bound checker for same-block scalar reborrows,
    with indexed access certificates and scaling checks.
  - operation identities carried through lowering into completed kernel reads
    and stores, including cached scalar reads; indexed bindings retain the
    actual pointer and reject another locked import identity. Failed writes
    produce no store observation, and source deltas have ambient-scaling checks.
  - the checked kernel lifecycle for exclusive scalar-reference identities:
    parent suspension, nested dependencies and one-time child recovery, with
    exact owned-support checks and indexed scaling regressions. The restricted
    source integration below now issues and consumes these transitions.
  - completed scalar-reborrow assignment receipts and execution-bound endings
    immediately after selected child stores. Bindings require both operations
    on one path, check the source and actual pointer, and refuse ambiguous
    repeated observations. These receipts do not yet carry local-loan leases
    or authorize recovery.
  - a private scalar-memory lease adapter that withholds the selected owner,
    checks custody in ordinary loads/stores, preserves child writes through
    recovery and rejects copied stale children after ownership returns. Kernel
    execution negatives and indexed adapter scaling checks cover this layer;
    restricted Rust source execution now activates it as described below.
    Calls, reference storage, aggregates and loop summarization remain refused
    while a lease is active.

  - source-bound births and explicit borrow-end operations for straight-line
    scalar borrow forests. An indexed alias/tree pass computes frontiers once;
    nested endings at one frontier run innermost first. Endings resolve live
    invocation handles, reject live children and consume each handle once,
    preserving the original owned support and current memory. Copies and moves
    retain the same identity, even after replacement of the original variable.
    Read/store observations remain read-only. Native store, alias, read-ending
    and nested-frontier fixtures cover helper/caller verification, expansion,
    parent reuse and authority/value negatives. Preparation scaling includes
    source length, aliases, nested depth and repeated shared diamonds.
    Structured acyclic branches now retain one exact live ledger through both
    arms and end at a common continuation. Arm accesses and conditions extend
    the frontier. Fully closed arm-local borrows/copies now use checked ledger
    checkpoints: all new references end, original ownership returns, private
    reference slots are cleared and the exact entry ledger is restored. Fresh
    IDs are not rewound. Nested scopes preserve existing live references and
    current writes; escaping or cross-arm references are refused. Source and
    selected-delta scaling cover this path. Native
    conditional and nested-borrow helpers/callers cover expansion and negatives,
    while kernel tests exercise joins with live custody.

  Wider source coverage remains open: escaping/conditionally live arm references,
  writes to outer reference bindings, early returns, loops, aggregates, shared
  borrow graphs and call/havoc transport
  need checked protocols. Only the
  activated source subset executes local leases. A reproduced false acceptance
  here would be `unsound`, and so P1, under the [roadmap rules](../roadmap/README.md).
- **Stable proof observations.** Provide source-facing slice, array and
  iterator observations, so that contracts need not depend on compiler
  temporary names or storage details. They must preserve qualified
  identities, shadowing, source spans, state meaning, and correspondence
  with expanded proofs.
- **Consistent library models.** Consolidate the supported resolved
  instances. Document their preconditions, effects, panic behavior and trust
  assumptions. Validate their declarations, and bind model versions into
  prepared identities. Lookalike methods must not acquire models by
  spelling.
- **Composition and scale.** Keep one execution path and shared CFG joins,
  compact repeated initialization, and checked cleanup on every supported
  exit. Add combined regressions, and verify that ordinary verification,
  profile, expansion and audit agree.
- **Broader coverage.** These stay outside the supported subset until a
  selected program needs a precise slice of them:
  - unsafe Rust and interior mutability;
  - returned references;
  - general traits and generics;
  - closures, async and threading;
  - heap support;
  - mutable or adapted iterators;
  - Cargo dependencies;
  - broad standard-library verification.
