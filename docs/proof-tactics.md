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

## Execution

| Surface form | Class | Meaning |
| --- | --- | --- |
| `step()` | smart | Advance one small C transition, selecting prerequisites and supported fact transports from context. |
| `step() using { P; ... }` | simple | Perform one transition using exactly the listed pure premises. An empty block is valid. |
| `execute()` | smart | Execute from the current frontier to function exit. It follows verified loop summaries and can plan explicit branch alternatives. |
| `execute_until(statement(N))` | smart | Execute forward to the selected statement entry without creating a new proof interface. |
| `summarize(loop(N))` | smart | Cross one already verified loop as an opaque transition, selecting its prerequisites contextually. |
| `summarize(loop(N)) using { P; ... }` | simple | Apply that loop summary using exactly the listed premises. An empty block is valid. |
| `reach(point) ensuring { ... } by { ... }` | control | Prove a scoped execution region and expose only its declared fact/resource interface at the target point. |

The boundaries are intentional: `step` is one transition, `summarize` is one
verified loop transition, `execute_until` repeats transitions to a point, and
`execute` runs to function exit. `reach` is a scoped proof and interface join,
not another spelling of repeated execution.

Expansion of execution automation uses `step() using` and `summarize using`,
including empty `using {}` blocks. The older branch-specific, budget-specific,
and certificate-oriented execution names are not part of the surface language.

## Proposition reasoning

| Surface form | Class | Meaning |
| --- | --- | --- |
| `simp()` | smart | Simplify the current proposition goal. It never executes C. |
| `assumption()` | simple | Close the goal from an exact available fact. |
| `normalize()` | simple | Close a context-free normalization goal. |
| `rewrite(P)` | simple | Rewrite with an exact available equality. |
| `intro()` | simple | Introduce an implication antecedent, negated proposition, or universal binder. |
| `split()` | simple | Close a conjunction when both conjuncts are exact available facts. |
| `left()` / `right()` | simple | Close the selected disjunct from an exact available fact. |
| `contradiction(P)` | simple | Close from exact facts `P` and `not P`. |
| `derive using { Q; ... }` | simple | Establish the current atomic proposition goal from exactly the listed premises using Click's deterministic atomic theories. |
| `apply(theorem(args))` | smart | Apply a theorem while selecting its premises from context. |
| `apply(theorem(args)) using { P; ... }` | simple | Apply a theorem using exactly the listed premises. |
| `induct(n) as ih` | simple | Start strong induction on a nonnegative `int32` theorem parameter. |
| `apply(ih(m))` | simple in an induction proof | Instantiate the local hypothesis after proving `0 <= m`, `m < n`, and the theorem requirements at `m`. |
| `have P by { ... }` | structural control; source class inherited | Prove `P` in a nested proof and add it to the surrounding context. |
| `if P { ... } else { ... }` | control | Split the proof on the exact condition `P`. This does not execute a C `if`. |
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

`derive` is the only public atomic-derivation tactic; `calculate` is not an
alias. Its target is always the current pure goal; repeating that proposition
inside the tactic is intentionally not accepted. The former `double_negation`
and `vacuous` leaves are ordinary
compositions: use `intro(); contradiction(P);`.

`have` has two classifications for two different questions. Its AST shape is
always control flow because it owns a nested goal. Its selectable source site
inherits SMART from a supported smart body, SIMPLE from a nonempty entirely
simple body, and is CONTROL otherwise. Profiling, smart-site discovery, and
expansion all use this source-site class.

When a smart `have` needs memory permissions merely to lower its goal, its
surface certificate retains the relevant loadability and order facts in an
explicit `derive using` block. A context-free-looking result such as a
normalized equality is not emitted as bare `normalize()` if replay still needs
those premises to interpret an indexed load. Verification checks the emitted
certificate immediately, and expansion/audit replay the same surface proof.

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
statement transitions are `step`, loop-summary transitions are `summarize`,
fact transports are `transport`, frame certificates are `frame`, and atomic
derivations are `derive`. A slow simple leaf is a Click performance bug. A
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
| `apply_loop_summary(...)` | `summarize(...)` |
| `execute_rest()` / `symbolic_execute()` | `execute()` |
| `execute_step()` | `step()` |
| `execute_then_step()` / `execute_else_step()` | smart `step()` or proof-level `if` |
| `bounded_execute()` | `execute()` or `by auto;` |
| `advance(...)` | `reach(...)` |
| `calculate(...)` | `derive using { ... }` |
| `double_negation()` / `vacuous()` | `intro()` followed by `contradiction(...)` |
