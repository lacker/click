# Proof tactics

This page is the reference inventory for Click's proof language. A tactic is
either **smart**, **simple**, or **control flow**:

- Smart tactics may inspect ambient facts, choose premises, split paths, or
  search for a proof. They are the tactics that `click profile` may recommend
  expanding.
- Simple tactics perform one deterministic rule from explicitly named data.
  They are the leaves emitted by `click expand` and should be fast.
- Control-flow tactics contain or join proof scripts. Their descendants, not
  the container itself, determine whether an expanded proof is simple.

`by auto;` and an omitted proof clause invoke the default orchestrator. They
are not script tactics. Successful smart tactics and `auto` retain the checked
surface provenance that `click expand` can render as an explicit proof.

For ordinary authoring, start with the omitted default, `by auto;`, or the
smallest comprehensible smart tactic. Use `click profile` before replacing a
smart tactic with an exact explicit proof. The simple forms below are public,
maintained Surface Click, but long `using` blocks are normally expansion output
rather than a recommended first draft.

Smart tactics are deliberately incomplete heuristics. A prompt failure means
that this search did not find a proof within its budget, not that Click's
engine is broken. Split a broad tactic into smaller operations or write the
relevant proof steps explicitly. Improve shared search only for a general,
measured proof pattern; do not tune it around each difficult proof. In
contrast, a smart success that cannot expand into normally verifiable source, a
missed deadline, or a proposition that cannot be expressed with simple tactics
is a tooling gap.

The **Verified success** column names a positive fixture exercised by the
ordinary gate. `docs/reference/tactics/fixtures.toml` maps every selectable
variant to an exact source needle; a bidirectional test rejects a new tactic
without a fixture or a stale mapping whose source no longer contains that use.

Condition-premise search is one such heuristic: it tries individual ambient
condition facts and pairs until it finds sufficient explicit premises or reaches
the active smart-tactic deadline. It does not discard facts after an arbitrary
context prefix. A normal miss reports the summarized target and recommends
smaller execution steps or exact premises; `simp() using { ... }` constrains
pure search to named facts, while a shorter run of `step();` lines isolates
the one execution transition that fails.

## Execution

| Surface form | Class | Valid state and transition | Failure, checking, and tools | Verified success |
| --- | --- | --- | --- | --- |
| `mark name;` | simple | At any live execution frontier, add a proof-local name for the current snapshot without advancing C. | A duplicate name fails. Click records the exact snapshot; expansion leaves the simple tactic unchanged, and profiling attributes only its bounded checking work. | [`proof_mark_current_frontier.md`](https://github.com/lacker/click/blob/master/mdtests/proof_mark_current_frontier.md) |
| `step()` | simple | At a live C frontier, execute the next statement with every fact in the proof context visible to the kernel. At a C `if`, an available condition fact selects and enters one arm; at a loop head, it evaluates the condition once and enters one iteration or advances past the loop. | A prerequisite the context cannot prove, or an unsupported transition, fails at that statement with that diagnostic. Click performs no premise search and carries no fact by list: a fact about a cell the context proves untouched keeps that cell's name. Expansion leaves the step unchanged, and profiling charges its one transition. | [`smart_step_carries_prior_call_facts.md`](https://github.com/lacker/click/blob/master/mdtests/smart_step_carries_prior_call_facts.md) |
| `execute()` | smart | From a live frontier, execute to function exit, following verified loop summaries and planning explicit branch alternatives. | A path that needs an unavailable rule or proof makes the tactic fail without a partial result. Click checks the complete planned execution; expansion emits explicit execution steps, and profiling attributes the smart plan and leaves. | [`tactic_execute.md`](https://github.com/lacker/click/blob/master/mdtests/tactic_execute.md) |
| `execute_until(statement(N))` | smart | From a live frontier, execute forward to the selected statement entry without creating a proof interface. | A backward, unreachable, branch-hidden, or function-exit target fails. Click checks every crossed transition; expansion prints those steps, and profiling reports the selected site. | [`execute_until_current_frontier.md`](https://github.com/lacker/click/blob/master/mdtests/execute_until_current_frontier.md) |
| `branch { [ensuring { ... }] then { ... } else { ... } }` | control | At a C `if` frontier, prove every feasible arm and join nonreturning arms into one continuation. The optional interface exports changed facts and resources. | A non-`if` frontier, overshot arm, unproved interface item, or nondeterministic join fails. Click follows the spelled arms and interface; expansion recurses into smart descendants, and profiling classifies those descendants. | [`frontier_branch.md`](https://github.com/lacker/click/blob/master/mdtests/frontier_branch.md) |
| `loop [as name] { ... }` | control | At a C loop frontier, prove initialization and one arbitrary iteration, construct the loop rule, and advance to its abstract exit. | A non-loop frontier or failed invariant, effect, or decrease obligation fails. Click checks the structural rule; expansion materializes omitted phase proofs, and profiling reports smart descendants and simple leaves. | [`count_to_n_loop_invariant.md`](https://github.com/lacker/click/blob/master/mdtests/count_to_n_loop_invariant.md) |

The boundaries are intentional: `step` is one concrete transition, `branch`
and `loop` unpack the corresponding C control flow at the current frontier,
`loop` constructs and applies one verified abstract loop transition,
`execute_until` repeats transitions to a program point, and `execute` runs to function
exit. A branch continuation executes once after its arm states have joined.

Marks are local to one proof and their names cannot be rebound. They remember
an already-reached state; they are not source labels, execution targets, or
saved states that can be restored. In particular, `execute_until(name)` does
not target a proof mark.

Expansion of execution automation emits one `step();` line per executed
statement, followed by the outcome closers. Expansion recurses through `loop` and materializes omitted
phase proofs at the loop keyword. The older numbered-loop summary syntax
remains migration compatibility and should not be used in new proofs.

## Proposition reasoning

| Surface form | Class | Valid state and transition | Failure, checking, and tools | Verified success |
| --- | --- | --- | --- | --- |
| `simp()` | smart | On a proposition goal, search ambient pure facts and bounded rules for a simple proof. It never executes C. | A bounded miss leaves the goal open and reports the target. Click checks the chosen operations; expansion prints its proof steps, and profiling reports search plus leaves. | [`simp_postconditions.md`](https://github.com/lacker/click/blob/master/mdtests/simp_postconditions.md) |
| `simp() using { P; ... }` | smart | On a proposition goal, search using exactly the listed proposition facts. | A missing fact or missing simple rule fails. Click uses the generated explicit proof rather than repeating search; expansion emits the named steps or reports the rule gap, and profiling reports the restricted site. | [`condition_search_explicit_decomposition.md`](https://github.com/lacker/click/blob/master/mdtests/condition_search_explicit_decomposition.md) |
| `assumption()` | simple | Close the current goal when an exact equal fact is available. | A merely derivable or differently spelled fact fails. Click performs exact lookup; expansion leaves the step unchanged, and profiling charges one simple leaf. | [`simple_tactics.md`](https://github.com/lacker/click/blob/master/mdtests/simple_tactics.md) |
| `extract(P)` | simple | Add `P` from an exact conjunction, or by bounded modus ponens from an available implication chain and exact antecedents. | A noncomponent or missing antecedent fails. Click follows the exact structural derivation with no search; expansion is unchanged, and profiling charges that derivation. | [`logical_tactics.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/tactic_tests/logical_tactics.rs) |
| `normalize()` | simple | Close a context-free proposition that normalizes to true. | Any goal that needs context fails. Click runs the deterministic normalizer; expansion is unchanged, and profiling charges the normalized expression. | [`simple_tactics.md`](https://github.com/lacker/click/blob/master/mdtests/simple_tactics.md) |
| `rewrite(P)` | simple | Rewrite the current proposition, including memory-resource ranges, with exact available equality `P`. | An absent equality, wrong direction with no exact match, or ill-typed rewrite fails. Click performs that rewrite only; expansion is unchanged, and profiling charges the affected expression. | [`simple_tactics.md`](https://github.com/lacker/click/blob/master/mdtests/simple_tactics.md) |
| `intro()` | simple | For an implication, negation, or universal goal, add the antecedent or named binder and continue with the body goal. | Any other goal shape fails. Click checks the one introduction rule; expansion is unchanged, and profiling charges one leaf. | [`copy_n_segment_invariant.md`](https://github.com/lacker/click/blob/master/mdtests/copy_n_segment_invariant.md) |
| `split()` | simple | Close a conjunction when both conjuncts are exact available facts. | Either missing conjunct fails; the tactic doesn't recursively prove them. Click performs two exact lookups; expansion is unchanged, and profiling charges one leaf. | [`logical_tactics.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/tactic_tests/logical_tactics.rs) |
| `left()` / `right()` | simple | Close the selected side of a disjunction from an exact available fact. | A missing selected fact fails even if the other side is available. Click checks the selected injection; expansion is unchanged, and profiling charges one leaf. | [`logical_tactics.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/tactic_tests/logical_tactics.rs) |
| `enumerate()` | simple | Close a constant-bounded universal from exact in-range instances or context-free vacuous guards, in range order. | An unbounded guard or missing instance fails. Click checks the explicit finite table with work proportional to it; expansion is unchanged, and profiling reports that work. | [`logical_tactics.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/tactic_tests/logical_tactics.rs) |
| `contradiction(P)` | simple | Close the goal from exact `P` and `not P`, including opposite polarities of one C condition. | Either missing polarity fails. Click performs exact indexed lookups; expansion is unchanged, and profiling charges one leaf. | [`surface_syntax.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/surface_syntax.rs) |
| `instantiate(F, value) using { P; ... }` | simple | Specialize exact universal fact `F` at `value`, discharge guards from only the listed premises, and add the conclusion. | An absent `F`, bad binder value, or undischarged guard fails. Click performs the named instantiation; expansion is unchanged, and profiling charges the explicit premises and result. | [`logical_tactics.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/tactic_tests/logical_tactics.rs) |
| `apply(theorem(args))` | smart | Apply a verified global theorem and select its proposition premises from context. | An unknown theorem, type mismatch, or bounded premise-selection miss fails without changing resources. Click checks the selected application; expansion adds `using`, and profiling reports search and leaves. | [`pure_theorem_apply.md`](https://github.com/lacker/click/blob/master/mdtests/pure_theorem_apply.md) |
| `apply(theorem(args)) using { P; ... }` | simple | Apply a verified global theorem using exactly the listed premises and add its guarantees. | Any missing requirement or mismatched argument fails. Click checks the exact application with no search; expansion is unchanged, and profiling charges its explicit input and guarantees. | [`produced_population_count_in_ensured_predicate.md`](https://github.com/lacker/click/blob/master/mdtests/produced_population_count_in_ensured_predicate.md) |
| `induct(n) as ih` | simple | As the first step of a pure theorem over nonnegative `int32` parameter `n`, introduce a strong induction hypothesis named `ih`. | A later position, nonparameter, or unproved nonnegative domain fails. Click opens the induction rule; expansion is unchanged, and profiling charges the structural setup. | [`pure_induction_countdown.md`](https://github.com/lacker/click/blob/master/mdtests/pure_induction_countdown.md) |
| `apply(ih(m))` | simple in an induction proof | Instantiate the local hypothesis after establishing `0 <= m`, `m < n`, and the theorem requirements at `m`. | A nondecreasing, negative, or requirement-violating argument fails. Click checks those exact obligations; expansion is unchanged, and profiling charges one local application. | [`pure_induction_countdown.md`](https://github.com/lacker/click/blob/master/mdtests/pure_induction_countdown.md) |
| `have P by { ... }` | structural control; source class inherited | Open a nested goal `P`; on success, add `P` to the surrounding context without changing its execution frontier. | Any unfinished nested goal fails and adds nothing. Click checks the nested proof; expansion recurses into it, and profiling classifies the source site from its body. | [`post_execution_have_checks_each_path.md`](https://github.com/lacker/click/blob/master/mdtests/post_execution_have_checks_each_path.md) |
| `if P { ... } else { ... }` | control | Split pure reasoning into contexts containing `P` and `not P`, then require both to prove the same goal. At an execution frontier each case runs its arm and then the shared continuation to its own function exit; the cases never rejoin as one state. | Either unfinished arm fails. Click checks both spelled branches; expansion recurses into smart descendants, and profiling reports them. | [`proof_if_cases.md`](https://github.com/lacker/click/blob/master/mdtests/proof_if_cases.md) |
| `cases (A or B) { ... } { ... }` | control | Eliminate an exact available disjunction, proving the goal once with `A` and once with `B`. | An unavailable disjunction or unfinished arm fails; this never substitutes `not A` for `B`. Click checks both arms, expansion recurses, and profiling reports descendants. | [`logical_tactics.rs`](https://github.com/lacker/click/blob/master/src/lang/click/tests/tactic_tests/logical_tactics.rs) |
| `open(resource) { ... }` | control | Temporarily replace a held composite resource with one body layer, check the nested proof, then fold it at scope exit. | Missing ownership, an undecided guard, or failure to restore the body fails. Click checks the exact resource transition; expansion recurses, and profiling reports descendants. | [`resource_population_open.md`](https://github.com/lacker/click/blob/master/mdtests/resource_population_open.md) |
| `witness(name = value)` | simple | On an existential goal, instantiate the named binder with `value` and continue with the instantiated body. | A wrong binder, ill-typed value, or nonexistential goal fails. Click records the exact witness; expansion is unchanged, and profiling charges one instantiation. | [`witness_and_choose.md`](https://github.com/lacker/click/blob/master/mdtests/witness_and_choose.md) |
| `choose(name from requirement(label))` | simple | From an exact existential requirement, introduce the named witness and its instantiated body into context. | An unknown label, wrong binder, or nonexistential fact fails. Click opens that exact fact; expansion is unchanged, and profiling charges one elimination. | [`witness_and_choose.md`](https://github.com/lacker/click/blob/master/mdtests/witness_and_choose.md) |

`by simp;` is sugar for a script containing the same `simp()` operation at the
same proof state. Neither form implicitly executes a function. Write
`execute(); simp();` when both operations are intended, or use `by auto;`.

`induct` is available only in a pure theorem, must be the first tactic, and
names a proof-local hypothesis. It is never inserted by `simp` or `auto`.
Although ordinary global-theorem `apply` is smart when it searches for
premises, applying the named induction hypothesis is a deterministic simple
step with fixed nonnegative, strict-decrease, and substituted-requirement
obligations.

`enumerate` is how an explicit proof closes a finite case analysis over a
constant-bounded universal, such as a `sorted(p, 3)` postcondition: the
expanded proof spells one `have` per non-vacuous instance (typically closed by
`intro`, `instantiate ... using`, an explicit transport, and `assumption`),
and `enumerate()` checks exactly those instances against the goal's own
guard-derived ranges. Click never instantiates by search: an in-range
instance that is neither vacuous nor spelled fails.

Proof-level `if` and `cases` answer different questions. `if P` is an
excluded-middle split: the else case assumes `not P`, so it cannot eliminate a
disjunctive fact whose right side is not the negation of its left. `cases`
requires the spelled disjunction to be an exact available fact and checks each
branch under exactly its assumed disjunct — the shape smart simplification
emits when a proof consumes a fact such as `selected == left or
selected == right`. Click never searches: a branch that needs the other
case's disjunct fails.

The retired `calculate` tactic is not an alias for simplification; use
`simp() using` to constrain smart search to named facts. The former
`double_negation` and `vacuous` leaves are ordinary compositions: use
`intro(); contradiction(P);`.

`have` has two classifications for two different questions. Its AST shape is
always control flow because it owns a nested goal. Its selectable source site
inherits SMART from a supported smart body, SIMPLE from a nonempty entirely
simple body, and is CONTROL otherwise. Profiling, smart-site discovery, and
expansion all use this source-site class.

When a smart `have` needs memory permissions merely to lower its goal, its
expanded proof retains the relevant loadability and order facts through
explicit transports, rewrites, extracts, or named theorem applications. A
context-free-looking result such as a normalized equality is not emitted as
bare `normalize()` if checking still needs those premises to interpret an
indexed load. A `simp() using` equality may be selected through a bounded chain
of exact equality facts whose intermediate load variables are kernel-internal
names for the same user-level loads. When frame evidence is needed to relate an
earlier load origin to the current one, the expanded proof first establishes the
current surface form with an explicit `transport`; simple `rewrite` checking
never searches for an equivalent equality. Expansion and audit verify the
complete rewritten surface proof through the ordinary entry point.

## Effects, resources, and snapshots

| Surface form | Class | Valid state and transition | Failure, checking, and tools | Verified success |
| --- | --- | --- | --- | --- |
| `frame()` / `frame(region)` | smart | On an effect or frame goal, select current range and effect premises and close the applicable condition. | A bounded premise-selection miss or real write outside the frame fails. Click checks the selected frame operations; expansion adds `using`, and profiling reports search and leaves. | [`fill_n_mutable_segment.md`](https://github.com/lacker/click/blob/master/mdtests/fill_n_mutable_segment.md) |
| `frame() using { P; ... }` | simple | Check the current frame condition from exactly the listed premises. The region form and an empty block are valid. | Missing coverage or separation evidence fails. Click performs no search; expansion is unchanged, and profiling charges the explicit region and premises. | [`conditional_ensure_modus_ponens.md`](https://github.com/lacker/click/blob/master/mdtests/conditional_ensure_modus_ponens.md) |
| `transport(P, Q)` | smart | When exact source `P` is available, derive target `Q` at another certified snapshot by selecting frame evidence. | Unrelated propositions, unsafe writes, or a bounded evidence miss fail. Click checks the chosen transport; expansion adds `using`, and profiling reports search and leaves. | [`simple_statement_step_explicit_transport.md`](https://github.com/lacker/click/blob/master/mdtests/simple_statement_step_explicit_transport.md) |
| `transport(P, Q) using { R; ... }` | simple | Derive target proposition `Q` from exact source `P` using only the listed snapshot and frame evidence. | An absent source, mismatched target, or insufficient evidence fails. Click checks that transport only; expansion is unchanged, and profiling charges the named evidence. | [`field_derived_precise_effect_after_metadata_write.md`](https://github.com/lacker/click/blob/master/mdtests/field_derived_precise_effect_after_metadata_write.md) |
| `unfold(name)` | simple | Replace an exact predicate fact or held supported resource with one definition body layer. | An unknown name, absent fact/resource, bodyless resource, or undecided guard fails. Click opens exactly one layer; expansion is unchanged, and profiling charges the produced body. | [`sorted_predicate.md`](https://github.com/lacker/click/blob/master/mdtests/sorted_predicate.md), [`composite_resource_composes_token.md`](https://github.com/lacker/click/blob/master/mdtests/composite_resource_composes_token.md) |
| `fold(resource)` | simple | Consume explicit current body facts and resources and produce the named composite resource. | A missing body member, false body fact, or undecided guard fails. Click folds exactly the named resource; expansion is unchanged, and profiling charges its body. | [`composite_resource_composes_token.md`](https://github.com/lacker/click/blob/master/mdtests/composite_resource_composes_token.md) |
| `observe(resource)` | simple | Keep a held composite folded while projecting its declared non-consuming view and immediate facts. | An absent resource or unsupported projection fails; owned contained resource facts never leak. Click performs one projection layer, expansion is unchanged, and profiling charges that layer. | [`composite_resource_folded_nested_fact_projection.md`](https://github.com/lacker/click/blob/master/mdtests/composite_resource_folded_nested_fact_projection.md) |
| `close_invariants()` | simple | At a loop back edge, discharge the explicit invariant bundle and finish the preservation transition. | Any missing invariant fact or resource fails. Click checks the bundle exactly; expansion is unchanged, and profiling charges the explicit invariants. | [`c_decreases_loop.md`](https://github.com/lacker/click/blob/master/mdtests/c_decreases_loop.md) |

Predicate calls are opaque to framing until their definitions are unfolded.
To carry such a fact across C execution, run `unfold(name)` before the relevant
steps and transport the unfolded definition.

`by frame;` is sugar for the same bare smart `frame()` at the same frontier. It
does not execute C. A whole-function explicit proof normally writes
`execute(); frame();`; `by auto;` may orchestrate both operations.

## Expansion, profiling, and audit

`click expand` replaces a selected smart tactic with its checked explicit
proof. Expanded proofs use only canonical surface names; internal
Rust variants such as certified statement transitions are not a second user
vocabulary. Expansion starts from a correct selected proof unit and verifies
that complete proof unit again after rewriting it. It does not emit a partial
rewrite when a later tactic in the same proof is failing.

`click expand --claim LABEL` applies the same checked rewrite to every smart
tactic in one function claim. This avoids manual site-by-site work when the
aggregate search cost is significant even though each smart tactic is prompt.

`click profile` reports smart and simple work under the same concepts:
statement transitions are `step`, checked loop transitions are `loop`,
fact transports are `transport`, frame operations are `frame`, and atomic
reasoning uses rules such as `assumption`, `normalize`, `rewrite`, and named
theorem applications. A slow simple leaf is a Click performance bug. A
successful slow smart tactic is an expansion candidate. An unsuccessful smart
tactic has nothing to expand; decompose that proof unless its search failed to
respect its bound or expose an actionable next step.

`click audit` finds smart tactics in a project, expands each one, and verifies
the rewritten source. Its purpose is to detect missing or invalid expanded
proofs, not to promise constant total verification time as a project
grows.

## Compatibility

Click has one spelling for each operation. Retired names are rejected with a
focused migration message:

| Retired | Use |
| --- | --- |
| `conjunction()` | `split()` |
| `apply_loop_summary(...)` / `summarize(...)` | frontier-local `loop { ... }` |
| `execute_rest()` / `symbolic_execute()` | `execute()` |
| `execute_step()` | `step()` |
| `execute_then_step()` / `execute_else_step()` | frontier-local `branch` |
| `bounded_execute()` | `execute()` or `by auto;` |
| `calculate(...)` | `simp() using { ... }` |
| `double_negation()` / `vacuous()` | `intro()` followed by `contradiction(...)` |
