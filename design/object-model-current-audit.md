# Current-master object-model audit

This audit separates current object-model mechanisms and executable evidence
from the retired PR #646 implementation. The source baseline is upstream
`20100ea35edb1c32622ef98884a503d11939e752`, fetched for this task on
2026-11-14 (America/Los_Angeles). At that baseline, the only executable addition was the small C++
output-initializer witness named below. Follow-up repairs and their evidence
are recorded separately below.

This is a bounded source and regression audit, not a soundness proof or a
full-language operation census. Test selection and results are recorded below. An existing C++ positive witness and a pointer-field resource fixture were
refused on this baseline. The getter and pointer-field repairs below supersede their baseline
results; the original audit counts remain historical.
Historical archive passes/failures are not counted as current results.

## Findings

1. Current master has useful shared pointer, construction, initialization and
   representation machinery. Rebuilding a universal object model is not the
   next prerequisite for using it.
2. Pointer address and designation are distinct in current values and proof
   rewriting. Subobject formation/access checks and complete pointer-cell reads
   have implementations and rejection witnesses. The archived design's claim
   that the scalar-sibling defect still needs implementation is historical.
3. Ordinary owned/viewed input is initialized input. Unwritten owned memory is
   separately expressible, and an initialized `produces` clause is checked on
   exit and transported to the caller. The C++ coverage roadmap's generic
   "needs an output-buffer contract" prerequisite was stale.
4. The selected native-interface laws still need a concise source-to-entry-to-call
   evidence matrix. The archive's `valid_place` and `native_record_inputs` /
   `native_span_inputs` implementation notes do not describe current master.
   Absence of those APIs is not itself a false acceptance: importer restrictions,
   shared typed access, actual call checks and resource contracts also constrain
   the admitted programs. A new semantic rule needs a concrete current witness.
5. Existing C++ tests separately establish modular byte writes into initialized
   storage and four direct byte writes completing a declared uint32. They do not
   by themselves establish the combination of a modular unwritten byte-output
   contract, the byte view and the caller's exact typed word observation. That
   composition remains a focused acceptance obligation.
6. At the original audit baseline, the C++ external-backing reference witness
   fails before its getter
   call: stable-view planning cannot supply the receiver loan. Its construction
   factory proof-mode check and destroyed-backing rejection both pass. This
   narrows the confirmed failure to that constructed-view call path; it does
   not demonstrate that destruction retires external backing.
7. At the audit baseline, `rb_produces_through_the_root_cell.md` failed while
   folding the produced resource after a pointer-field store. The repair below
   restores this small witness with its original C and contract and explicit
   ownership-derived frame facts in its proof. Larger rbtree sidecars remain
   separate acceptance work.
8. Rbtree reports contain later frontiers than the old roadmap summary. The
   pointer-cell representation repair is already implemented; its original
   large sidecars are not established green. No new full rbtree census or
   historical regression count is claimed here.

## Current implementation and witnesses

The implementation paths below are current-master paths. The witnesses are
regressions, not an assertion that every operation in the same category works.

| Obligation | Implementation inspected | Named evidence / boundary |
| --- | --- | --- |
| Pointer identity and rewriting | `kernel/primitives.rs`, `kernel/proof/term_rewrite.rs`, `kernel/proof/term_rewrite/pointer_application_tests.rs` | Numeric rewrites preserve origin/extent; full rewrites do not adopt unrelated read carriers; shared-DAG scaling controls exist. |
| Formation and subobject access | `kernel/eval/operators.rs`, `kernel/eval/memory_loads.rs`, `languages/cpp/lowering.rs` | `cpp_forming_a_pointer_two_past_a_scalar_member_is_refused.md`, `cpp_a_member_reference_parameter_keeps_its_subobject.md`, `cpp_an_unknown_pointer_needs_bounds_even_without_a_dereference.md`. Bounds apply before dereference. |
| Pointer fields and calls | `surface/proof/resources.rs`, shared memory observation and call transitions | `stored_pointer_identity_survives_resource_call.md`, `a_stored_member_pointer_keeps_its_subobject.md`, `a_member_pointer_returned_by_a_call_keeps_its_subobject.md`; original rbtree report remains separate. |
| Raw and reference results | `languages/cpp/lowering.rs`, `kernel/functions/call_arguments.rs` | `cpp_pointer_returns_preserve_identity_and_modular_results_offline`, `cpp_native_reference_results_preserve_aliases_and_require_backing_authority_offline`. A returned address does not grant backing authority. |
| Construction and copying | `kernel/functions/construction_return.rs`, `languages/cpp/construction.rs` | `aggregate_return_tests`: exact destinations through factories, aliasing without freshness, uninitialized-source rejection, join/substitution and temporary retirement. `record_copy_keeps_self_pointer_value_without_rebasing_it` checks C++ source admission. |
| Initialization and joins | `surface/lowering/resource_lowering.rs`, shared initialized-memory state | `naming_symbolic_construction_storage_does_not_initialize_it`, `symbolic_construction_initialization_survives_havoc_and_intersects_at_join`; ownership and naming cannot substitute for writes. |
| Modular initialization | `surface/parser.rs`, `surface/lowering/resource_lowering.rs`, `kernel/functions/call_initialization.rs`, produced-memory transfer in `kernel/functions.rs` | `an_initializer_produces_the_memory_it_initialized.md`, `produces_refuses_memory_the_function_did_not_write.md`, `verified_call_initialization_tests`, and the new `cpp_initializer_produces_written_memory.md`. |
| Lifetime and backing | `languages/cpp/lifetime.rs`, construction retirement and allocation generations | `cpp_reference_into_destroyed_local_backing_cannot_be_read_offline` passes. `cpp_external_backing_reference_survives_descriptor_destruction_offline` failed at the getter call before destruction on the original baseline and passes after the metadata repair below. Its writable counterpart passes too. |
| Typed/byte values | `kernel/eval/byte_view.rs`, `kernel/tests/byte_view_tests.rs`, byte-representation design | Complete declared uint32 assembly, partial-write refusals, same-state observations and no byte forging of pointer cells. This is a selected target rule, not arbitrary retyping. |
| Native type admission | `languages/cpp/schema.rs`, `languages/cpp/validity.rs`, `languages/cpp/scalar.rs`, parameter lowering | Checked record identities and layouts, supported reference/pointer forms, authenticated `std::byte`, restricted casts; `cpp_native_pointer_artifacts_reject_pointee_substitution_offline` and `nested_record_artifacts_reject_wrong_identity_extent_constness_and_cycles`. This is not yet the full interface matrix below. |

All source paths in the table are relative to `src/`; Markdown witnesses are
in `mdtests/`, and named C++ tests are in `tests/cpp_import.rs` unless stated
otherwise. `design/aggregate-construction.md`,
`design/pointer-subobject-extents.md`, and
`docs/internals/byte-representation.md` describe the delivered bounded rules.

## Constructed-view getter: baseline failure and repair

Run the existing named test, not the entire nightly suite:

```sh
source /workspace/.click-tools/activate.sh
export CLICK_CPP_EXPORTER="$PWD/target/cpp-exporter/click-cpp-exporter"
RUST_MIN_STACK=8388608 cargo nextest run --lib --features fast-gate \
  --run-ignored all \
  -E 'test(=gate_tests::cpp_import::cpp_external_backing_reference_survives_descriptor_destruction_offline)'
```

The source and complete sidecar are retained unchanged in
`tests/cpp_import.rs::check_cpp_descriptor_backing_lifetime(false)`. The source
pattern is a `View` constructor storing `int* data`, `get() const` returning
`*data`, and `run` returning `view.get()` before its local descriptor is
destroyed. `run` views the external `data[0..1]`; the getter views both the
pointer field and its backing cell.

At the original audit baseline, the test exits unsuccessfully with this
planning refusal:

```text
run.contract tactic 0: step() could not verify C operation:
stable-view the required loan backing or binding is missing refused during planning;
selected resource views view[0]
C operation: __click_cpp_nested_value_0 = __cpp_q_I4_View_I3_get((view as (int32 *)))
```

The reported context includes the caller's `views data[0]`, the constructed
`owns view[0..8]`, and the pointer-field equality to `data`. The refusal is at
the getter call, before local destruction. There is no `goal:` line for a
specific unproved proposition. Under the tracing procedure this is an
`unclear-trace` outcome; the internal cause was not yet established. No new bug file or GitHub issue was filed.
The unchanged witness remains in the test suite. The follow-up below resolves
this frontier without changing the C++ or contracts.

### Repair: preserve byte identity across object metadata

A follow-up reproduces the failure on upstream `3cd0f9491`. Removing the
destructor passes, but adding an unrelated local declaration to that passing
case fails again. Returning only the stored pointer, without reading through
it, passes. Thus the descriptor field is readable; the missing evidence is
for reborrowing its external backing after extra declarations, including
cleanup's compiler-generated captures.

`record_memory_derivation` now retains the predecessor's byte-read identity for
`BlockDeclared` and `ObjectInitializationRecorded`, as it already does for
byte-preserving observation/cache transitions. These edges write no values.
The current state still supplies type, lifetime, initialization and access
checks. An actual write retains its distinct identity; neither numeric address
equality nor a metadata transition manufactures a loan or ownership.

The original read-only and writable descriptor-destruction tests now pass,
including their selected expansion/cold/retained checking and hostile-contract
controls. The existing destroyed-local-backing rejection still passes. A fast
kernel regression checks complete pointer designation/address identity across
both metadata edges, distinct initialization states, absence of read authority,
and refusal to identify a pointer after an upper-half byte write. The existing
read-identity production scaling regression now includes declaration and
initialization metadata at 8/32/128/512 steps; endpoint work remains bounded.

The pre-integration checks pass all 369 selected memory/loan/construction and
search-boundary tests and all 1,616 active scaling tests. Final integration
validation is recorded in the fix PR. The whole object-model item remains open;
this repair does not claim its remaining interface or byte-output evidence.

## Pointer-field resource fold: baseline failure and repair

Run the unchanged fixture alone:

```sh
MDTEST_FILTER=rb_produces_through_the_root_cell RUST_MIN_STACK=8388608 \
  cargo nextest run --lib --features fast-gate \
  -E 'test(=gate_tests::mdtests::mdtests)'
```

The baseline audit first encountered it in the `MDTEST_FILTER=produces_` group; all
other ten selected fixtures passed. The full C, resources and proof remain in
`mdtests/rb_produces_through_the_root_cell.md`. The body stores `node` in
`root->rb_node`; its contract produces the tree through that root field.
The baseline failure was at `rb_set_root.contract` tactic 4 (`fold`):

```text
a generated prerequisite has no Surface spelling; this is a spellability defect
goal: at(<state A>, root->rb_node) == <pointer A>
```

`<state A>` is the memory after the store to `root->rb_node`; the report does
not define `<pointer A>` in its legend. This prevents stating the generated
link from the report (`unclear-trace` under the tracing procedure). The
reproduction establishes a current tooling/composition failure, not a false
acceptance or a root cause in pointer designation. No new bug file or issue
was filed. Keep this exact fixture as the small acceptance witness rather
than substituting a full rbtree census.

The follow-up repair starts from `c221cda33dbaed982c351ff32eb5fda18d56a934`
and is integrated onto `a8b40fddd2cead1bee34a07a72d6da99c05feb21`.
The store itself was already working. Prerequisite reconstruction now retains
proof-local binder names in a persistent index updated from changed bindings;
spells 64-bit reads at their retained interpretation; keeps full Click operands
through casts; and selects recorded array-argument memories and pointer reads
by their defining states. The round-trip checks remain in place, and no
kernel inference or fact-dependent lowering was added.

The C, resource definitions and function contract are unchanged. The proof
states three `separate(memory(...), memory(root->rb_node))` facts, each proved
by `known()`, before the store. These expose the existing ownership frame
for the metadata, left-child and right-child cells. Omitting them still
exhausts the implicit closer's budget; this repair does not claim complete
implicit frame discovery.

`pointer_field_resource_fold_preserves_match_binders_across_proof_modes`
checks ordinary verification, expansion, retained replay, cold checking of the
expanded claim with implicit solving disabled, and refusal of a body that
stores null. It is a named nightly regression. Focused source tests cover
binder shadowing/forks, signed and unsigned word reads, casted calls, and
recorded array states. The gate covers 32/64-bit calls; the complete
ten-format sweep is a named nightly check. Multi-size controls grow binder/alias populations
and unrelated recorded history. This does not close the larger rbtree reports
or replace the remaining native-interface matrix.

Delivery validation on the integrated branch: all 1,635 active scaling tests,
the selected source/proof-object and documentation tests, seven named C++
compatibility tests, and 14 selected resource fixtures pass. The combined
source/scaling/documentation/Rust run has 1,915 passes and nine Rust tests that
stop during frontend setup because this environment lacks the pinned Charon
bundle; those nine do not reach verification. The full nightly suite was not
run. The focused proof-mode regression above passes separately.

## Remaining interface audit

Do not assume an archived native validity field exists upstream. For each row,
trace the current source restriction, lowered parameter/result metadata,
symbolic entry and actual modular call. Reuse passing tests above, adding only
witnesses for uncovered distinctions.

| Native interface | Evidence to account for before claiming closure |
| --- | --- |
| Scalar reference | Binding/address formation versus value read; constness, subobject bounds, unwritten scalar and dead backing at the caller. A C++ reference binding alone must not initialize its referent. |
| Record reference / receiver | Authenticated record and field layout, containing/member bounds, constructor phase and actual caller permissions. Scalar carrier width is not the record's nominal validity. |
| Raw pointer | Null or unused forwarding must not need a live referent; arithmetic/access needs its own domain and backing. An equal address through another carrier cannot supply designation. |
| By-value record | Check the source before materialization, preserve pointer fields and nested subobject boundaries, keep the fresh copy distinct from pointees. |
| Constructor destination | Bind the original destination once, preserve parent/sibling footprints, check value fields rather than initializing padding, and carry only checked completion to callers. |
| Pointer/reference result | Preserve complete identity and bounds across summary/call/substitution; tie access to independently live backing and caller authority. |

This is remaining evidence work, not a claim of six reproduced defects. Do not
introduce a keyword or revive archived metadata merely to check off a row.

## Validation

The audit used the pinned Rust 1.98.1 toolchain, a fresh worktree/target directory,
`RUST_MIN_STACK=8388608`, and an exporter built from the same revision with
`scripts/build-cpp-exporter.sh`. The test binary was built with
`cargo nextest list --lib --features fast-gate --message-format json`. After
that build, nextest reused its binary and Cargo metadata while the independent
documentation build ran. No old-worktree executable supplied these results.

| Selection | Result |
| --- | --- |
| `kernel::functions::aggregate_return_tests`, `verified_call_initialization_tests`, `kernel::tests::byte_view_tests`, `kernel::proof::term_rewrite::pointer_application_tests`, and corresponding pointer-application scaling tests | 69 passed, including selected multi-size and rejection controls. |
| C++ uninitialized-read, modular ownership/initialization, pointee-substitution, reference qualification, self-pointer copy, constructor factory expansion/retained checking, external-backing and destroyed-backing tests | Seven passed; the external-backing getter positive failed as recorded above. The two tests cancelled by the first fail-fast run were subsequently selected and passed. |
| Four named pinned-byte tests in `tests/bitcoin_core_money_range.rs`: `pinned_std_byte_modular_pointer_call_verifies_offline`, `pinned_std_byte_reinterpretation_initializes_uint32_offline`, `pinned_std_byte_reinterpretation_does_not_initialize_partial_storage`, `pinned_std_byte_reinterpretation_requires_original_storage_ownership` | Four passed. These separately check modular initialized-byte writes, direct word assembly, partial initialization and missing authority. |
| `cpp_mdtest_imports_match_the_pinned_exporter`, with `CLICK_REFRESH_CPP_IMPORTS=1` | Passed; generated the new initializer's locked import; existing imports unchanged. |
| 70 distinct Markdown fixtures across the selections below | 69 passed; the root-cell produced-resource fixture failed as recorded above. Overlapping filter selections are counted once. |

The Markdown selections were `cpp_initializer_produces_written_memory`,
`cpp_a_member_reference_parameter_keeps_its_subobject`,
`cpp_a_member_reference_returned_by_a_call_keeps_its_subobject`,
`cpp_an_unknown_pointer_needs_bounds_even_without_a_dereference`,
`cpp_forming_a_pointer_two_past_a_scalar_member`, `cpp_record_pointers`,
`cpp_new_delete`, `stored_pointer_identity_survives_resource_call`,
`resource_uint64_entry_cell_fold`, `byte_representation_`, `produces_`,
`uninitialized_`, `aggregate_copy_uninitialized_source_rejected`, and
`a_join_leaves_a_local_uninitialized`, each as `MDTEST_FILTER` with
`cargo nextest run --lib --features fast-gate -E 'test(=gate_tests::mdtests::mdtests)'`.
Named ignored tests were selected explicitly; the full nightly suite was not run.

The full gate, complete rbtree directory, all Rust frontend paths and the
retired branch were not run. The focused run is deliberately not a green-tree
verdict: it reproduced the two failures above. A skipped test is not passing
evidence. `scripts/check.sh --docs-only` passed all 44 documentation tests,
book rendering and structural lint; advisory Vale lint was unavailable.

## History and retired obligations

PR #646 and its fork archive preserve the attempted implementation. The old
[recovery audit](https://github.com/clicklang/click/blob/8b1b20e7a/design/object-model-recovery-audit.md)
and [recovery roadmap](https://github.com/clicklang/click/blob/8b1b20e7a/roadmap/object-model.md)
preserve the chronological experiments and old example counts. The
[pre-cleanup current roadmap](https://github.com/clicklang/click/blob/20100ea35/roadmap/object-model.md)
records the already-retired branch and later rbtree checklist. They are not
current upstream support declarations.

There is no remaining requirement to revive that branch, bisect every discarded
change, reproduce its internal APIs, or make its example count green. Its
semantic laws remain in `cpp-object-model.md`; their active acceptance scope is
[the object-model roadmap](../roadmap/object-model.md). Bitcoin serialization,
additional lifetime features and owning containers belong to their coverage
items. Current rbtree defects remain with their existing reports and launch
milestone, with current reproductions rather than inherited counts.
