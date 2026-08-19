# WIP fallout log

## nested_field_segments_keep_the_terminal_field_offset (first audit)

The write's `execute` now needs the defining equation (`v == load`) as a
theorem premise and fails: "condition-certificate premise search did not
derive int32 equality is true from 0 ambient condition facts: []". The
defining fact rides the CExpressionPath fact stream, but the
condition-certificate premise search consults an ambient condition-fact
channel that is empty at that point. Fix direction: route the defining
fact into the channel the premise search consults (find where
"condition-certificate premise search" collects its ambient facts and
whether path facts should feed it), or emit the defining fact earlier so
assumptions_with_path_context carries it into step certification. This
symptom likely underlies several of the 14 — verify against the next
tests before fixing one-off.

## Layer 1 fixed: the defining fact is certified, not derivable

`ExecutionPureFact::certified` (not `::new`) marks the defining equation
as kernel-certified by construction — the fresh variable is the kernel's
own name for the load. The "assumption-derived theorem premise without a
replayable derivation" class disappears across the affected tests.

## Layer 2 surfaced: kernel variables need surface spellings

Next failure class: "kernel fact has no recorded or structurally
synthesized Click spelling: ConditionIs(PointerOffsetEqual(Int32Scaled {
value: Variable(..)" — surface synthesis (frame certificate lowering)
must spell facts mentioning the minted variable. The fix direction:
when synthesizing a spelling for a kernel variable, resolve it through
its defining fact to the load's recorded surface spelling
(surface_synthesis-side), or record a surface alias at mint time via
the replay's surface record (lang-side plumbing at the drain boundary).
Re-diagnose the outcome-match class (Variable(2) vs certification
spelling) after this layer: the certified flag may have changed it too.

## Layer 2 progressed: substitution-based spelling, round-trip resolved

`resolve_minted_load_variables` (kernel/reasoning/substitution.rs,
exported) rewrites minted variables to their defining loads before
surface synthesis at the four surface_replay sites, and the round-trip
check now accepts a lowering that matches the resolved fact. Both
mechanisms work.

## Layer 3 surfaced: frame evidence bridges the two spellings

The remaining failure fact is
`ConditionIs(PointerOffsetEqual(Int32Scaled{Variable(v)},
Int32Scaled{MemoryLoad(..)}))` — smart-frame evidence relating the
minted-variable spelling of an address to its load spelling. Under
substitution it degenerates to a self-equality and its synthesized
spelling re-lowers as a TypedLoad fact — structurally unmatchable. The
right question is upstream: this premise is derived from the defining
equation (kernel bookkeeping, certified family) and plausibly should
never be surfaced as a user-facing frame premise at all, exactly as
certified store equations are not. Next session: read the smart-frame
candidate construction to find where premises are collected and whether
certified-derived offset equalities should be filtered into the ambient
channel instead of the surfaced premise list.

## Layer 3 fixed: bookkeeping derivations filtered from frame premises

Frame-certificate lowering now skips derivations whose conclusion
resolves to a syntactically reflexive equality under defining-fact
substitution (`proposition_is_reflexive_equality` after
`resolve_minted_load_variables`): those bridge the minted and load
spellings of one address, replay re-mints them deterministically, and
they are certified bookkeeping rather than Click-visible premises.

## Layer 4: outcome matching needs the equation chain

The test now reaches the outcome-match class: replay produces
`Return(Constant(7))` while kernel certification spells the outcome
differently, and pairing fails. The bridge needs chaining through the
defining equation and the store equation (v == load == value); check
whether `outcomes_match`'s definitional equality chains two equations or
needs the defining facts normalized into direct value equalities first
(normalize_direct_atomic_memory_loads exists nearby in the simp premise
path and may be the intended tool).

## Layer 4 infrastructure landed; the finding is fact flow

Two sound mechanisms are in: mint memoization (one canonical variable
per (snapshot arena id, pointer) — repeated loads reuse the name, so
self-relations stay syntactic) and `resolve_minted_load_pointer`
(range/containment provers rewrite a minted query address to its load
spelling before matching load-spelled owned ranges; wired into
`memory_write_range`). The decisive probe: the resolver finds ZERO
defining-shaped facts in the write check's assumptions during kernel
certification — the equation minted at lvalue evaluation is not in the
statement's fact context downstream. The next thread is execution fact
flow: where the lvalue path's facts go between evaluation and the
store's effective assumptions in the certification pass, and whether
defining facts need the persistent channel that certified store
equations use rather than the per-path stream. Also noted: the index
side of `data[len]` still embeds the raw len-load (pointer ADDITION
builds offsets outside the canonicalized helper), so the arithmetic
birth census needs the pointer-plus-int operator path added.

## Layer 4 continued: reuse-from-assumptions in, shape mismatch remains

The mint now searches ambient assumptions for an existing binding of the
same load (same pointer, same snapshot handle) and reuses that variable
before minting — the mechanism that should make the executed address and
the contract-spelled owned range coincide. It does not yet connect: the
lead test still certifies to MissingResource, so the contract's
variable-to-load linkage is not spelled as
`ConditionIs(Bitvector32Equal(Variable, MemoryLoad))` in the write
check's assumptions (or the snapshot handles differ between the entry
binding and the current-memory load). Next: dump the actual proposition
shapes mentioning the contract variable in this test's entry facts
(grounding, not guessing — candidate shapes include `CMemoryLoads`,
`Equal`, or a TypedLoad-anchored form), then widen the reuse match to
that shape, bridging entry-to-current memory through the existing
unchanged-load machinery if the handles differ.

## Layer 4 closed: content-addressed canonical load variables

The MissingResource class was a three-way spelling split for one load:
contract-grant lowering (surface, raw `MemoryLoad(empty-placeholder)`),
requirement evaluation (kernel mint from one counter), and body execution
(kernel mint from another counter). Counter-based minting cannot unify
passes that share no allocator state, so the mint is now content-addressed:
`canonical_load_variable(memory, pointer)` hashes the load identity into a
reserved id space (base 2^40, precedent `spec_fold_bound_variable`), with a
thread-local registry that panics on a hash collision between distinct
identities instead of silently conflating them. All three birth paths —
`mint_canonical_load_variable` (eval + spec) and the surface
`symbolic_pointer_contract_memory_load` — now call it, so every pass spells
the same load with the same variable and containment is syntactic. The
counter threading is now vestigial (parameters retained, unused) and can be
removed in cleanup. Lead test passes; suite fallout dropped 14 → 6.

## Remaining fallout classes (6 tests)

1. **Snapshot-unstable naming** (`truncated_service_step…`, likely the
   perpetual-service and simp-premise tests): the same cell loaded at two
   snapshots hashes to two canonical variables, where raw load spellings
   were previously bridged by atomic-load provenance seeing through the
   terms. Fix direction: canonicalize the load term to its
   provenance-stable spelling (store-equation / placeholder resolution,
   the existing `canonicalize_atomic_loads` layer) before hashing, so
   unchanged cells share one name across snapshots.
2. **No surface spelling for canonical variables in expansion**
   (`modular_call_snapshot_anchor…`, expansion tests): fact transports over
   defining equations have no recorded Click spelling. Same family as the
   layer-2 fix; extend the resolved round-trip or synthesize spellings for
   defining facts. The transport source also shows an un-canonicalized
   load born through the pointer-ADD operator path (worklist item).

## Snapshot-stable naming: canonical spelling + registry view (6 -> 4)

Two refinements landed. First, the canonical variable id now hashes the
provenance-stable spelling (`canonicalize_atomic_loads`) rather than the
raw term, so representational snapshot differences share one name. Second,
assumption-based cross-snapshot equalities (call-havoc boundaries) cannot
be hashed away, so equality reasoning views a registered canonical
variable as the load it names at the three trigger points
(`bitvector_terms_equal_for_memory_resolution`, the chase-pair check in
assumptions.rs, and `memory_load_terms_equal_for_fact_transport`),
letting the existing provenance evidence fire exactly as it did for load
spellings. The perpetual-service and truncated-service tests pass again.

Remaining (4): the resource-neutral-callee allocation fold and the
expansion separation `have` still miss — some resource/separation
matching path bypasses the widened equality; and the two expansion
transport tests need Click surface spellings for defining equations.
Also watch: full-suite time moved 19s -> 34s on one run; measure whether
the canonical-view recursion on the hot equality path is responsible
before integration.

## Frontier: resource-neutral-callee moved to the exit claim check

After the registry view landed, this test's failure moved past the fold:
the error is now `unverified claims: Ensure(0) = produces Composite
allocated(owner)` from src/lang/click/verification.rs:1120, and none of
the kernel MissingResource probes fire. Established so far: composite
candidate selection is spelling-insensitive (`exact_shapes` keys on
family/name/arity, resource_algebra.rs:656), so the miss is either in
`resource_fact_entails` argument-equality proving or — more likely given
the new error site — in the surface-level claim satisfaction comparison,
which may match produced claims structurally rather than through the
prover. Next: find where Ensure claims are matched against
replay-established claims in verification.rs and check whether the
comparison is structural; if so, decide whether to canonicalize claim
spellings at lowering or route the comparison through proof-aware
resource entailment.

Remaining failures (4): this one; expansion separation `have`
(source_expander_derives_separation_from_call_postconditions); and the
two expansion transport spelling tests (modular_call_snapshot_anchor,
snapshot_bridged_simp_premise) which need Click surface spellings for
canonical-variable defining equations. Probes still in tree: statements/
expression/functions MissingResource sites, resource_algebra write-miss
probe — remove before integration.

## Defining equations leave the path wraps (4 -> 3)

The resource-neutral-callee failure traced to `wrap_path_context`: call
postcondition equalities were being wrapped as
`Implies(defining-equation, equality)`, and the resource argument
equality path (`pointer_offsets_equal_for_memory_resolution` ->
`exact_condition_value`) does not discharge implications. A canonical
defining equation is true by construction of the naming, so both wraps
(`wrap_proof_facts`, `wrap_path_context`) now skip
`is_canonical_load_defining_fact` propositions, leaving consequents
unguarded and reachable by exact fact lookup. Suite time back to ~22s.
Remaining: the three expansion tests (transport spellings for canonical
variables, separation have).
