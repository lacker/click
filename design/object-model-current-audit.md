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
2. Pointer address and provenance are distinct in current values and proof
   rewriting. Subobject formation/access checks and complete pointer-cell reads
   have implementations and rejection witnesses. The archived design's claim
   that the scalar-sibling defect still needs implementation is historical.
3. Ordinary owned/viewed input is initialized input. Unwritten owned memory is
   separately expressible, and an initialized `produces` clause is checked on
   exit and transported to the caller. The C++ coverage roadmap's generic
   "needs an output-buffer contract" prerequisite was stale.
4. The native-interface matrix below now pairs source admission, symbolic body
   entry and actual-call checks with positive and rejection witnesses. The
   archive's `valid_place` and native-input APIs are not implementation
   requirements. Its selected laws are enforced through current metadata,
   shared access checks, explicit resources and supported-source restrictions.
5. The modular byte-output composition below now checks unwritten-byte output,
   the authenticated byte view and the caller's exact typed word observation
   together. This closes the small foundation case, not general byte retyping
   or Bitcoin serialization coverage.
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
| Pointer identity and rewriting | `kernel/primitives.rs`, `kernel/proof/term_rewrite.rs`, `kernel/proof/term_rewrite/pointer_application_tests.rs` | Numeric rewrites preserve origin/bounds; full rewrites do not adopt unrelated read carriers; shared-DAG scaling controls exist. |
| Formation and subobject access | `kernel/eval/operators.rs`, `kernel/eval/memory_loads.rs`, `languages/cpp/lowering.rs` | `cpp_forming_a_pointer_two_past_a_scalar_member_is_refused.md`, `cpp_a_member_reference_parameter_keeps_its_subobject.md`, `cpp_an_unknown_pointer_needs_bounds_even_without_a_dereference.md`. Bounds apply before dereference. |
| Pointer fields and calls | `surface/proof/resources.rs`, shared memory observation and call transitions | `stored_pointer_identity_survives_resource_call.md`, `a_stored_member_pointer_keeps_its_subobject.md`, `a_member_pointer_returned_by_a_call_keeps_its_subobject.md`; original rbtree report remains separate. |
| Raw and reference results | `languages/cpp/lowering.rs`, `kernel/functions/call_arguments.rs` | `cpp_pointer_returns_preserve_identity_and_modular_results_offline`, `cpp_native_reference_results_preserve_aliases_and_require_backing_authority_offline`. A returned address does not grant backing authority. |
| Construction and copying | `kernel/functions/construction_return.rs`, `languages/cpp/construction.rs` | `aggregate_return_tests`: exact destinations through factories, aliasing without freshness, uninitialized-source rejection, join/substitution and temporary retirement. `record_copy_keeps_self_pointer_value_without_rebasing_it` checks C++ source admission. |
| Initialization and joins | `surface/lowering/resource_lowering.rs`, shared initialized-memory state | `naming_symbolic_construction_storage_does_not_initialize_it`, `symbolic_construction_initialization_survives_havoc_and_intersects_at_join`; ownership and naming cannot substitute for writes. |
| Modular initialization | `surface/parser.rs`, `surface/lowering/resource_lowering.rs`, `kernel/functions/call_initialization.rs`, produced-memory transfer in `kernel/functions.rs` | `an_initializer_produces_the_memory_it_initialized.md`, `produces_refuses_memory_the_function_did_not_write.md`, `verified_call_initialization_tests`, and the new `cpp_initializer_produces_written_memory.md`. |
| Lifetime and backing | `languages/cpp/lifetime.rs`, construction retirement and allocation generations | `cpp_reference_into_destroyed_local_backing_cannot_be_read_offline` passes. `cpp_external_backing_reference_survives_descriptor_destruction_offline` failed at the getter call before destruction on the original baseline and passes after the metadata repair below. Its writable counterpart passes too. |
| Typed/byte values | `kernel/eval/byte_view.rs`, `kernel/tests/byte_view_tests.rs`, byte-representation design | Complete declared uint32 assembly, partial-write refusals, same-state observations and no byte forging of pointer cells. This is a selected target rule, not arbitrary retyping. |
| Native type admission | `languages/cpp/schema.rs`, `languages/cpp/validity.rs`, `languages/cpp/scalar.rs`, parameter lowering | Checked record identities and layouts, supported reference/pointer forms, authenticated `std::byte`, restricted casts; `cpp_native_pointer_artifacts_reject_pointee_substitution_offline` and `nested_record_artifacts_reject_wrong_identity_size_constness_and_cycles`. The completed interface matrix below distinguishes entry and actual-call evidence. |

All source paths in the table are relative to `src/`; Markdown witnesses are
in `mdtests/`, and named C++ tests are in `tests/cpp_import.rs` unless stated
otherwise. `design/aggregate-construction.md`,
`design/pointer-subobject-bounds.md`, and
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
specific unproved proposition. Under the proof repair procedure this is an
`unclear-output` outcome; the internal cause was not yet established. No new bug file or GitHub issue was filed.
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
kernel regression checks complete pointer provenance/address identity across
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

The baseline failure was also reproduced on upstream `2175760b9` on
2026-11-15 in 0.85 seconds, without changing verifier, C or sidecar.
The baseline audit first encountered it in the `MDTEST_FILTER=produces_` group; all
other ten selected fixtures passed. The full C, resources and proof remain in
`mdtests/rb_produces_through_the_root_cell.md`. The body stores `node` in
`root->rb_node`; its contract produces the tree through that root field.
The baseline failure was at `rb_set_root.contract` tactic 4 (`fold`):

```text
a generated prerequisite has no Surface spelling; this is a raise-lower principle defect
goal: at(<state A>, root->rb_node) == <pointer A>
```

`<state A>` is the memory after the store to `root->rb_node`; the report does
not define `<pointer A>` in its legend. This prevents stating the generated
link from the report (`unclear-output` under the proof repair procedure). The
baseline reproduction established a tooling/composition failure, not a false
acceptance or a root cause in pointer provenance. No new bug file or issue
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
by `close()`, before the store. These expose the existing ownership frame
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
or replace the native-interface checks recorded below.

Delivery validation on the integrated branch: all 1,635 active scaling tests,
the selected source/proof-object and documentation tests, seven named C++
compatibility tests, and 14 selected resource fixtures pass. The combined
source/scaling/documentation/Rust run has 1,915 passes and nine Rust tests that
stop during frontend setup because this environment lacks the pinned Charon
bundle; those nine do not reach verification. The full nightly suite was not
run. The focused proof-mode regression above passes separately.
### Report naming follow-up

Full error reports now format an unresolved prerequisite with the same retained
proof naming context as the rest of the diagnostic and the concise CLI report.
The original report had discarded that context for the prerequisite, printing
`<pointer A>` even though the match binder `identity` was retained. The fact is
expressible as `root->rb_node == identity`; its explicit rewrite proof checks.
This report fix is independent of the prerequisite reconstruction repair above;
it changes no proof checking or synthesis. The repaired fixture is the
acceptance witness for the fold behavior.


## Modular byte-output composition

The witness in `tests/fixtures/cpp-byte-output/initialize.cpp` declares an
uninitialized `unsigned int`, passes its `std::byte*` view to `fill`, and returns
the word. `fill` retains four `p[i]` stores. Its sidecar consumes four unwritten
bytes, produces them initialized and states each byte's value. The source is
checked against the authenticated pinned libstdc++ declaration and reloaded
offline.

The first failure was exporter admission of builtin scalar pointer subscripts.
They now use the existing pointer-add and load/store artifact nodes, retaining
written operand order for `p[i]` and `i[p]`. Shared bounds, initialization and
write-permission checks still apply. The next failure was the exact word value:
output initialization and all four byte facts already transferred, but no rule
connected them to the caller's typed word observation.

A checked complete four-byte output clause for a live declared uint32 under
the installed little-endian layout now supplies its representation equation:
that state's typed read is the four unsigned byte reads zero-extended and
shifted by 0, 8, 16 and 24 bits. The shared output-initialization transition
adds the equation after marking the returned bytes initialized. It leaves load
terms unchanged and supplies no initialization or authority of its own.
Selection uses the explicit output clause, declaration and five fixed read
identities, with no fact search or memory scan. Ordinary pointer and local
reads produce no extra representation facts. Other types, partial value runs,
untyped blocks, ended objects and unsupported byte orders stay outside this rule.

`pinned_std_byte_modular_output_initializes_uint32_offline` proves `0x12345678`
after the modular call, expands the proof, cold-checks it with implicit solving
disabled for `probe.contract`, and replays it in a retained session. Controls
refuse a missing write, missing write permission and reuse of a pre-call zero
observation. The existing consistently rehashed forged-byte artifact controls
check nominal identity, declaration location, underlying type and locked header
authority. Kernel tests independently check state, type, lifetime and target
selection. The native pointer-store test retains `*(p + 1)` and adds `p[1]` and
`1[p]` for unsigned word/byte loads and stores, including read-only refusal.

The rule names the selected state's typed read directly at the selected
output transfer, preserving ordinary C/Rust reads and their expression roots. Its multi-size
control grows unrelated memory at 8, 32, 128 and 512 blocks. The scalar-ownership
control uses cold sessions and nonempty contexts at every size, retaining its
tight work bound and deliberately injected scan refusal.


The first local byte-output checks passed, but CI exposed excess work from
attaching this equation to ordinary word reads. Moving production to the
selected output transfer restores the ordinary read path. The completion
validation below includes the formerly failing retained-memory and Rust cases.

## Writable-byte span composition

`tests/fixtures/cpp-byte-output/span.cpp` constructs a genuine pinned
`std::span<std::byte>` over an unwritten caller uint32, copies the descriptor
into a body-checked helper, writes four elements through `operator[]`, and
returns the exact word `0x12345678`. Its sidecar consumes four unwritten bytes,
produces four initialized bytes, and specifies each byte. Descriptor state and
backing authority remain separate.

Four repairs make these boundaries compose:

- `library/cpp/span.interface.click` supplies the dynamic pointer/count constructor's
  explicit library assumption. It initializes the descriptor, with no grant
  of backing ownership. Signature selection excludes static extent, iterator
  pairs and other count types.
- `R.parameter(name)` field reads retain flattened nested record paths.
  libstdc++ stores span length inside `_M_extent`, so a precondition about the
  copied descriptor previously had no round-tripping Surface spelling even
  though the equality checker knew its value. The smaller `span-size` fixture
  isolates this boundary without byte writes.
- Output initialization and empty external-write-footprint checking use the
  address class's unique concrete storage anchor. An authenticated descriptor
  alias can therefore initialize the original word and identify a write to
  this function's local storage. The checked transfer still supplies bounds,
  lifetime and authority; integer address equality grants none of them.

- Native byte and halfword read observations retain their own widths when a
  word or pointer has also been read at that address. Previously the wider
  observation could suppress narrow-read equality registration during retained
  replay, although ordinary and cold checking succeeded.

Design check: the field reader does work in its explicit access path and the
selected layout. The two fast checking changes use the existing indexed
storage-anchor query, keyed by the selected output/write address, without
walking aliases or memory history. Native narrow widths come from the explicit
load kind and use the existing indexed observation registry. Lowering never
chooses a term from facts.
The new deterministic controls grow unrelated memory and the selected address's
equality history at 8, 32, 128 and 512 entries.

`pinned_writable_byte_span_modular_output_initializes_uint32_offline` checks the
ordinary proof, expanded cold checking with implicit solving disabled for
`probe.contract`, and retained replay. It refuses a short call, an out-of-span
index even with enough physical backing, missing write permission and a missing
byte. `pinned_writable_byte_span_output_requires_live_backing_offline` copies a
span over a helper's local word into an external descriptor: observing its size
remains valid after that backing expires, while writing through it or exporting
ownership of the expired bytes is refused. Kernel controls also keep external
storage writes outside an empty mutable footprint.

This is a four-byte composition witness under the pinned little-endian profile.
It does not establish Bitcoin cursor/serialization verification or broaden the
word-representation rule to other storage or scalar types. The separate
`pinned_writable_byte_span_by_value_preserves_pointer_state` witness now proves
both the returned pointer and the byte length for an unchanged by-value
`as_writable_bytes` wrapper. Its explicit proof links the private parameter
copy to the library result, then preserves both descriptor fields through the
checked return and parameter retirement. Saved points name the private
aggregate storage rather than the caller image; construction-return footprints
include private parameter cleanup. Copy returns retain their source until
materialization. The regression checks expansion, strict cold checking and
retained replay with implicit solving disabled.

## Bitcoin read32 serialization composition

The pinned Bitcoin v31.1 `ser_readdata32<FixtureReader>` graph now imports
unchanged, including its nested pointer/count span construction,
`as_writable_bytes` construction return, the fixture reader call and
`le32toh_internal`. `tests/fixtures/cpp-byte-output/bitcoin-read32.cpp` defines
the fixture reader separately from Bitcoin source. It copies four source
bytes to the output span and advances its pointer/count cursor. It does not
stand for Bitcoin's `SpanReader` or its exception behavior.

The complete selected graph has a positive serialization witness in
`pinned_bitcoin_read32_serialization_verifies_offline`: the unchanged reader
copies all four bytes, the serializer's local `uint32_t` becomes `0x12345678`,
`le32toh_internal` returns that word, and the wrapper proves the same result
and both cursor updates. The contracts retain the source view, destination
initialization transfer, exact byte values and pointer/count outcomes.

The proof matrix expands all four source bodies and compares the generated
`bitcoin-read32-expanded.click` fixture for freshness. A separate cold check
requires no smart sites and verifies that complete source with implicit solving
disabled. Four separate retained-session tests replay each body's certificate
with implicit solving disabled. Negative controls remove or shorten the source
view, remove output permission, shorten the output span, change a source byte,
change the serialized result, or demand the wrong cursor advance.

The former uninitialized read was an initialization-bookkeeping defect. Input
pointer-field observations could precede the marker for unwritten output.
Forgetting their cached values after a store retained initialization only for
automatic storage; the subsequent external read therefore lost evidence it
already had. Dropped observed cells and run slots now retain that evidence
whenever an unwritten-object marker makes later reads check initialization.
This grants no new ownership or view, initializes no unobserved bytes, and
preserves the compact recording of contiguous constant-offset runs. Unit
controls cover absent/partial observations and unwritten output; deterministic
scaling grows unrelated cached cells and dropped runs through 65,536 slots.

The reader spells each store's footprint separation and carries source bytes,
previously written output bytes and the remaining count through individual
transitions. Footprint normalization retains scoped address congruence while
accepting resource separation only from its selected premises; controls cover
missing separation, missing aliases and insufficient spans. Deterministic
scaling grows alias and separation buckets.

Composition also requires unsigned-word pointer fields to survive by-value
copies, construction-return span fields to retain their names, saved copied
parameter pointers to retain their element widths, and declared output storage
to remain addressable before initialization. These are checked operations and
type metadata; none grants backing authority. Dynamic-extent
`as_writable_bytes(std::span<unsigned int>)` now uses the same stated library
template as the existing `int` profile. Construction-result field metadata is
shared across calls with indexed reads and a deterministic scaling regression.

The next application boundary is Bitcoin's real throwing cursor. This fixture
does not cover `SpanReader`, malformed-input exceptions, arbitrary serialization
formats or general C++ object lifetimes.

The delivered prerequisites are narrower:

- Function-template arguments can name admitted trivial record declarations;
  their legacy keys use declaration identity rather than a flattened name.
  Same-layout `left::Stream` and `left_Stream` instantiate distinct functions.
- Nonthrowing statement calls can construct a trivial record temporary,
  forward a construction-return temporary into one stable direct receiver
  call, and retire the temporaries in reverse construction order at the full
  expression. Constructors must preserve copied argument values. Storage
  observation, throwing consumers and unsupported copy returns remain refused.
- Const native pointer arithmetic and byte reads support the fixture's input.
  Write-through-const restrictions are unchanged.
- Stated fixed-span separation survives pointer copies through an exact
  address-class/byte-span index. It preserves width orientation on class
  merges and refuses overlap. A resource prerequisite naming a loaded pointer
  field uses that field's declared pointer type, including byte pointers.

The generic record-temporary witness checks ordinary, expanded cold and
retained modes, plus a false-result control. Constructor eligibility scales
at 8/32/128/512 fields and call sites; exact separation lookup scales with
unrelated facts, same-pair widths and alias history at the same sizes. The
spelling regression round-trips byte, halfword, int32 and uint64 pointer fields.
The existing writable-span composition still passes its complete proof modes
and rejection controls. The separate by-value returned-span witness also
preserves pointer and length through parameter retirement, as described above.
This selected composition is not evidence for restoring the archived universal
object model.

## Native-interface evidence matrix

This closes the bounded entry/call audit for the supported native profiles.
It is an account of the rules the selected witnesses exercise, not a full C++
soundness proof. Source admission, a symbolic body's assumptions and an actual
call's obligations are separate boundaries. Pointer carriers never establish
initialization, access authority or complete record validity by themselves.

All implementation paths below are relative to `src/`. Named C++ witnesses
are in `tests/cpp_import.rs`; Markdown witnesses are in `mdtests/`.

| Interface | Source admission and symbolic body entry | Actual caller boundary | Evidence |
| --- | --- | --- | --- |
| Scalar reference | `languages/cpp/{schema,scalar,interface,lowering}.rs` check the resolved reference type and constness, retain a separate address carrier and expose the referent under its source name. Binding supplies an address, not an initialized value or owner. Ordinary `views`/`owns` clauses promise initialized input; explicit unwritten storage does not. | `CheckedObjectAddress` in `kernel/eval/expression.rs` checks the complete referent's bounds and live storage without reading its value. Call-resource transfer and `functions/call_initialization.rs` check the resources and initialized input the callee actually requires. A later read still needs initialization; writes need mutable authority. | R1, R2, R3 below. |
| Record reference / receiver | `languages/cpp/schema.rs` checks record declaration identity, layout, field paths, callee signature and root constness. `interface.rs::function_interface` retains record/layout metadata; `lowering.rs` projects fields with their subobject bounds. The int32-pointer execution carrier is not the record's footprint. Entry field resources, not the carrier width, justify accesses. | A projected method/reference argument retains the selected child or scalar extent. The caller must establish the callee's leaf resources, guards and sibling separation. A readable sibling or numerically equal address cannot replace the selected field. Const roots cannot become mutable receivers. | O1, O2 below and R3. |
| Raw pointer | `languages/cpp/{schema,scalar,interface}.rs` check the supported pointee/profile and preserve pointer identity. A raw pointer argument may be null and can be forwarded without any backing resource. Its signature alone promises no dereferenceable storage. | `kernel/eval/operators.rs` checks pointer arithmetic's domain before a dereference; `eval/expression.rs`, memory loads and call-resource transfer check bounds, backing lifetime and permissions at access. Return identity is not a backing grant. | P1, P2 below. |
| By-value record | Only the admitted trivial copy profile is used; nontrivial copy/move bodies and unsupported prvalues are refused. `lowering.rs` retains the aggregate layout; `functions/call_arguments.rs` gives symbolic entry an independent evaluated field image with private field storage. Pointer fields remain values pointing at their original backing. | `functions/globals_and_aggregates.rs::aggregate_argument_read_refusal` checks the source's full extent, field read permissions and initialization before binding the callee's private copy. Even a source field the callee does not inspect is copied and must be readable. Copy ownership grants no ownership of pointees. | V1, V2 below. |
| Constructor destination | `languages/cpp/schema.rs` requires the checked member-initializer prefix in declaration order, complete value-field initialization and the correct embedded constructor identity. `lowering.rs` marks the construction parameter and layout. Constructor entry receives the selected raw destination; field ownership there does not pretend its values are already written. | `functions/construction_return.rs::{destination,bind,complete_parameter}` checks original destination, layout, alignment, size, lifetime and writable value fields. Completion checks that original storage even if the parameter is reassigned. It does not initialize padding or resize the containing allocation. Parent fields and backing remain independently framed. | C1, C2 below. |
| Pointer/reference result | `languages/cpp/{schema,interface,lowering}.rs` retain the result category, native type and qualification. Shared call/result handling carries the complete pointer identity and provenance, rather than inventing a pointee from its address. | The caller independently justifies reference formation and every subsequent access. Returned member bounds survive calls. Destroying a local descriptor does not retire its external backing; destroying the actual backing prevents a read. A dangling alias may escape under an alias-only/trivial claim, so a reference result is not an unconditional promise of live backing. | T1, T2 below and R3. |

### Named positive and rejection pairs

- **R1 — binding versus initialization:**
  `cpp_native_interface_reference_binding_does_not_initialize_storage_offline`
  calls an alias-only `identity(int&)` on an unwritten scalar. Binding without
  reading succeeds; writing through the returned reference makes the later
  scalar read return 7. Removing the write while retaining the read is refused
  as uninitialized. Both positives check ordinary verification, a selected
  expanded certificate, independent cold verification and retained replay.
- **R2 — qualification and required authority:**
  `const_reference_preserves_qualification_and_may_alias_a_mutable_reference`,
  `cpp_const_reference_results_preserve_native_qualification_offline` and
  `cpp_native_reference_results_preserve_aliases_and_require_backing_authority_offline`
  cover aliasing, read permissions, qualification mismatch and forged result
  metadata. An alias-only contract cannot prove a referent value.
- **Record reference results:** `cpp_record_reference_results_*` cover direct
  and forwarded nominal record references, mutable and const call-result local
  aliases, result fields, nested member identity, pointer-backed results and
  forged call-capture types. They check ordinary verification, expansion,
  strict cold checking and retained replay; returned addresses grant no
  authority or lifetime extension. The nested getter and forwarding fixture
  writes through the returned reference while preserving a sibling view.
  Its proof uses the returned pointer's retained identity and the checked
  domain supplied by the getter's equality.
- **R3 — member boundaries at actual calls:**
  `cpp_reference_formation_rejects_one_past_even_under_trivial_postconditions`
  pairs a one-past refusal with a larger-backed positive.
  `cpp_a_member_reference_parameter_keeps_its_subobject.md` and
  `cpp_a_member_reference_returned_by_a_call_keeps_its_subobject.md` refuse
  accessing an adjacent sibling through the member reference even when the
  caller also views that sibling.
- **O1 — record layout and projected calls:**
  `nested_record_declarations_preserve_layout_identity_and_offline_field_frames`
  and `projected_record_calls_and_reference_arguments_verify_offline` check
  nested records, method receivers and scalar/record reference arguments.
  `nested_record_artifacts_reject_wrong_identity_size_constness_and_cycles`
  and `projected_call_artifacts_check_target_identity_and_root_constness`
  reject consistently rehashed nominal/layout/callee/qualification forgeries.
- **O2 — caller authority and frames:**
  `projected_call_contracts_require_leaf_authority_and_preserve_sibling_frames`
  rejects the wrong leaf owner, read-only authority for a write, missing guards
  and false sibling claims. `projected_calls_keep_cpp_constness_and_source_profile_boundaries`
  records source refusals, including mutable calls through const roots.
  `inherited_method_and_reference_calls_verify_offline_with_sibling_frames`
  supplies the admitted bounded inherited-call witness; this is not general
  inheritance coverage.
- **P1 — forwarding and null:**
  `cpp_pointer_returns_preserve_identity_and_modular_results_offline` verifies
  `identity(data)` for an unconstrained raw pointer with no backing resource.
  `cpp_literal_null_pointer_values_verify_without_storage_authority_offline`
  checks native null spellings; `cpp_literal_null_pointer_dereference_requires_live_backing_offline`
  refuses the actual `read(nullptr)` call.
- **P2 — arithmetic and provenance:**
  `cpp_unknown_pointer_formation_requires_bounds_before_any_dereference`
  pairs an unbounded arithmetic refusal with a backed one-past result.
  `cpp_forming_a_pointer_two_past_a_scalar_member_is_refused.md` and
  `cpp_an_unknown_pointer_needs_bounds_even_without_a_dereference.md`
  check formation separately from a memory read. Equal-address rewrites do not
  erase the bounds in the member-reference witnesses.
- **V1 — source reads at the value boundary:**
  `cpp_native_interface_record_copy_checks_every_source_field_offline` proves
  the ordinary `take(source)` call, then refuses missing read authority and an
  unwritten unused source field. The positive checks expansion, cold checking
  and retained replay. `trivial_record_parameter_copy_keeps_caller_fields_and_shared_backing`
  and its expanded/retained counterpart keep the caller's descriptor unchanged
  while allowing a separately authorized pointee write; read-only pointee
  authority is refused. The original descriptor-copy C++ and contract are
  unchanged; its proof now states the unchanged size/data fields and the new
  backing value with three `close()` steps before the return arithmetic. This
  does not claim complete implicit discovery of those facts.
- **V2 — copy identity and source admission:**
  `record_copy_keeps_self_pointer_value_without_rebasing_it` refuses rebasing
  a copied self-pointer to the destination. `trivial_record_parameter_copy_refuses_nontrivial_move_and_prvalue_arguments`
  records explicit source exclusions. The copy-call witness also rejects forged
  copy kind, source place, record identity and unlocked source span.
- **C1 — real embedded destinations:**
  `embedded_member_constructor_preserves_parent_fields_and_backing_offline`
  verifies embedded construction and independently expands the child, parent
  and caller contracts; forged initializer order, reinitialization, field,
  arguments and callee are refused. `embedded_constructor_preserves_self_pointer_identity_offline`
  checks a child at a nonzero parent offset.
- **C2 — completion and factory calls:**
  `construction_return_descriptor_factories_expand_and_retain_offline` checks
  actual modular construction/copy chains. Shared-kernel
  `aggregate_return_tests::construction_parameter_completion_checks_original_storage`
  pairs complete and partial constructors, keeps padding unwritten, and refuses
  completing another object by reassigning the destination parameter.
  `raw_object_footprint_does_not_resize_or_initialize_parent_storage` checks the
  containing allocation separately. `constructor_local_rejects_throwing_partial_and_reordered_forms`
  records the corresponding C++ source/admission boundary.
- **T1 — results retain identity and qualification:** P1 and R2 exercise actual
  modular pointer/reference returns and false identity/value claims.
  `cpp_field_reference_results_preserve_addresses_and_backing_authority_offline`
  checks an actual caller writing through a returned field reference; R3 checks
  the returned member bounds.
- **T2 — independently live backing:**
  `cpp_external_backing_reference_survives_descriptor_destruction_offline` and
  its writable counterpart keep external backing after descriptor cleanup.
  `cpp_reference_into_destroyed_local_backing_cannot_be_read_offline` accepts
  the alias-only escape but rejects the value observation after cleanup.

### Supported boundary and closure

These rows establish evidence for the admitted native scalar/pointer/reference,
trivial record-copy and bounded construction profiles. Ordinary readable
resources promise initialized input; explicit unwritten resources and checked
output initialization remain distinct. No universal `valid_place` predicate or
archived native-input metadata is required to justify the selected operations.
The byte bridge uses the selected pinned compiler/LP64 little-endian
representation model; it is not a blanket C++20 retyping guarantee. Standard-
library contracts remain explicit assumptions. The record-reference-local
follow-up (`cpp_record_reference_locals_*`) checks mutable/const aliases,
`ref.field`/`&ref` spelling, nested record members, non-reading pointer binding,
permission refusals and storage retirement with expanded and retained replay.
Unsupported result categories, nontrivial copy/move bodies and the broader
source forms listed in the C++ coverage item remain outside these witnesses.

They do not establish arbitrary casts/retyping, byte-built pointers, broader
lifetime replacement, union punning, general inheritance, additional targets,
owning containers or Bitcoin serialization. Unsupported source forms above
are explicit refusals, not delivered functionality. Keep these laws as
requirements of each later C++ slice in `roadmap/cpp-support.md`.

The getter, pointer-field fold and modular byte-output acceptance cases have
named proof-mode and hostile controls above. With this matrix's entry/caller
pairs, the bounded object-model roadmap item has no remaining implementation
checklist. Larger rbtree sidecars and C++ feature coverage retain their own
existing work items.

### Completion validation

On the integrated `b22678f9f` completion branch, all 78 selected matrix checks
and all 1,669 active scaling tests pass. Seven focused checks cover the modular
byte-output proof modes and the six previous CI regressions (retained native
memory, Rust core-method work bounds, Option and Vec). All 41 selected Markdown
fixtures pass with zero observed fact-stability differences, including the
member-reference boundaries, initialization, pointer/resource compatibility,
root-cell fold and 29 byte-representation fixtures. All 44 documentation tests,
Rust/scaling-file format checks, mdBook and documentation lint pass.

The stored-pointer resource-call fixture now targets `call(helper, 0)` instead
of relying on six source steps. Its C and contract are unchanged. The full
nightly suite was not run; only named relevant nightly checks were selected.

## Original audit validation

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
[the native-interface matrix](#native-interface-evidence-matrix). Bitcoin serialization,
additional lifetime features and owning containers belong to their coverage
items. Current rbtree defects remain with their existing reports and launch
milestone, with current reproductions rather than inherited counts.
