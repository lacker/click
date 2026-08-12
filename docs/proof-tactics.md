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
are not script tactics. Successful smart tactics and `auto` retain checked
surface certificates that `click expand` can print and replay.

For ordinary authoring, start with the omitted default, `by auto;`, or the
smallest comprehensible smart tactic. Use `click profile` before replacing a
smart tactic with an exact certificate. The simple forms below are public,
maintained Surface Click, but long `using` blocks are normally expansion output
rather than a recommended first draft.

Smart tactics are deliberately incomplete heuristics. A prompt failure means
that this search did not find a certificate within its budget, not that Click's
engine is broken. Split a broad tactic into smaller operations or write the
relevant simple steps explicitly. Improve shared search only for a general,
measured proof pattern; do not tune it around each difficult proof. In
contrast, a smart success that cannot expand and replay, a missed deadline, or
a proposition that cannot be expressed with simple tactics is a tooling gap.

Condition-certificate search is one such heuristic: it tries individual
ambient condition facts and pairs until it finds replayable premises or reaches
the active smart-tactic deadline. It does not discard facts after an arbitrary
context prefix. A normal miss reports the summarized target and recommends
smaller execution steps or exact premises; `simp() using { ... }` constrains
pure search to named facts, while `step() using { ... }` names one exact
execution transition.

## Execution

| Surface form | Class | Meaning |
| --- | --- | --- |
| `mark name;` | simple | Name the current frontier state for later `at(name, ...)` expressions. It does not move execution. |
| `step()` | smart | Advance one small C transition, selecting prerequisites and supported fact transports from context. |
| `step() using { P; ... }` | simple | Perform one transition using exactly the listed pure premises. An empty block is valid. |
| `execute()` | smart | Execute from the current frontier to function exit. It follows verified loop summaries and can plan explicit branch alternatives. |
| `execute_until(statement(N))` | smart | Execute forward to the selected statement entry without creating a new proof interface. |
| `branch { [ensuring { ... }] then { ... } else { ... } }` | control | Consume the C `if`, prove its feasible arms, and join them into one continuation state. The optional interface exports facts and resources about changed state. |
| `loop [as name] { ... }` | control | Verify the C loop exactly at the current frontier, apply its checked rule, and advance to its abstract exit. |

The boundaries are intentional: `step` is one concrete transition, `branch`
and `loop` unpack the corresponding C control flow at the current frontier,
`loop` constructs and applies one verified abstract loop transition,
`execute_until` repeats transitions to a point, and `execute` runs to function
exit. A branch continuation executes once after its arm states have joined.

Marks are local to one proof and their names cannot be rebound. They remember
an already-reached state; they are not source labels, execution targets, or
saved states that can be restored. In particular, `execute_until(name)` does
not target a proof mark.

Expansion of execution automation uses `step() using`, including empty
`using {}` blocks. Expansion recurses through `loop` and materializes omitted
phase proofs at the loop keyword. The older numbered-loop summary syntax
remains migration compatibility and should not be used in new proofs.

## Proposition reasoning

| Surface form | Class | Meaning |
| --- | --- | --- |
| `simp()` | smart | Simplify the current proposition goal. It never executes C. |
| `simp() using { P; ... }` | smart | Search for a proof using exactly the listed proposition facts. Expansion either emits named simple steps or reports the missing simple proof rule. |
| `assumption()` | simple | Close the goal from an exact available fact. |
| `extract(P)` | simple | Add `P` when it is a proper conjunct of an exact available conjunction. |
| `normalize()` | simple | Close a context-free normalization goal. |
| `rewrite(P)` | simple | Rewrite the current proposition, including memory-resource ranges, with an exact available equality. |
| `intro()` | simple | Introduce an implication antecedent, negated proposition, or universal binder; an introduced binder is available by its Click name to following tactics. |
| `split()` | simple | Close a conjunction when both conjuncts are exact available facts. |
| `left()` / `right()` | simple | Close the selected disjunct from an exact available fact. |
| `contradiction(P)` | simple | Close from exact facts `P` and `not P`, including exact opposite polarities of the same C condition. |
| `instantiate(F, value) using { P; ... }` | simple | Specialize an exact available universal fact `F` at `value`, discharging each instantiated guard from the listed premises alone (by normalization or one bounded atomic derivation), and add the instantiated conclusion. |
| `apply(theorem(args))` | smart | Apply a theorem while selecting its premises from context. |
| `apply(theorem(args)) using { P; ... }` | simple | Apply a theorem using exactly the listed premises. |
| `induct(n) as ih` | simple | Start strong induction on a nonnegative `int32` theorem parameter. |
| `apply(ih(m))` | simple in an induction proof | Instantiate the local hypothesis after proving `0 <= m`, `m < n`, and the theorem requirements at `m`. |
| `have P by { ... }` | structural control; source class inherited | Prove `P` in a nested proof and add it to the surrounding context. |
| `if P { ... } else { ... }` | control | Split the proof on the exact condition `P`. This does not execute a C `if`. |
| `cases (A or B) { ... } { ... }` | control | Eliminate an exact available disjunction: the first block proves the goal assuming `A`, the second assuming `B`. Both blocks are always spelled. |
| `witness ...` / `choose ...` | control | Introduce or select existential evidence in the supported proposition contexts. |

`by simp;` is sugar for a script containing the same `simp()` operation at the
same proof state. Neither form implicitly executes a function. Write
`execute(); simp();` when both operations are intended, or use `by auto;`.

`induct` is available only in a pure theorem, must be the first tactic, and
names a proof-local hypothesis. It is never inserted by `simp` or `auto`.
Although ordinary global-theorem `apply` is smart when it searches for
premises, applying the named induction hypothesis is a deterministic simple
step with fixed nonnegative, strict-decrease, and substituted-requirement
obligations.

Proof-level `if` and `cases` answer different questions. `if P` is an
excluded-middle split: the else case assumes `not P`, so it cannot eliminate a
disjunctive fact whose right side is not the negation of its left. `cases`
requires the spelled disjunction to be an exact available fact and checks each
branch under exactly its assumed disjunct — the shape smart simplification
emits when a proof consumes a fact such as `selected == left or
selected == right`. Replay never searches: a branch that needs the other
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
surface certificate retains the relevant loadability and order facts through
explicit transports, rewrites, extracts, or named theorem applications. A
context-free-looking result such as a normalized equality is not emitted as
bare `normalize()` if replay still needs those premises to interpret an
indexed load. A `simp() using` premise that equates one expression across
several execution snapshots may denote an available fact only through the
kernel's certified snapshot bridge; the certificate then materializes that
spelling with an explicit `transport` before citing it, because simple
`rewrite` replay never searches for an equivalent equality. Verification
checks the emitted certificate immediately, and expansion/audit replay the
same surface proof.

## Effects, resources, and snapshots

| Surface form | Class | Meaning |
| --- | --- | --- |
| `frame()` / `frame(region)` | smart | Prove the applicable effect/frame condition while selecting range and effect premises contextually. |
| `frame() using { P; ... }` | simple | Check the frame condition using exactly the listed premises. The region form and an empty block are valid. |
| `transport(P, Q)` | smart | Re-spell an available fact across certified execution snapshots, selecting frame evidence contextually. |
| `transport(P, Q) using { R; ... }` | simple | Perform that transport using exactly the listed evidence. |
| `unfold(name)` | simple | Unfold a predicate or supported resource definition. |
| `fold(resource)` | simple | Fold a supported resource definition from explicit current facts/resources. |
| `observe(resource)` | simple | Project the declared non-consuming view of a held composite resource. |
| `close_invariants()` | simple | Discharge the explicit invariant bundle at a loop back edge. This is mainly certificate-facing. |

Predicate calls are opaque to framing until their definitions are unfolded.
To carry such a fact across C execution, run `unfold(name)` before the relevant
steps and transport the unfolded definition.

`by frame;` is sugar for the same bare smart `frame()` at the same frontier. It
does not execute C. A whole-function explicit proof normally writes
`execute(); frame();`; `by auto;` may orchestrate both operations.

## Expansion, profiling, and audit

`click expand` replaces a selected smart tactic with its checked simple
certificate. Printed certificates use only canonical surface names; internal
Rust variants such as certified statement transitions are not a second user
vocabulary. Expansion starts from a correct selected proof unit and verifies
that complete proof unit again after rewriting it. It does not emit a partial
rewrite when a later tactic in the same proof is failing.

`click profile` reports smart and simple work under the same concepts:
statement transitions are `step`, checked loop transitions are `loop`,
fact transports are `transport`, frame certificates are `frame`, and atomic
reasoning uses rules such as `assumption`, `normalize`, `rewrite`, and named
theorem applications. A slow simple leaf is a Click performance bug. A
successful slow smart tactic is an expansion candidate. An unsuccessful smart
tactic has nothing to expand; decompose that proof unless its search failed to
respect its bound or expose an actionable next step.

`click audit` finds smart tactics in a project, expands each one, and verifies
the rewritten source. Its purpose is to detect missing or invalid Click
certificates, not to promise constant total verification time as a project
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
