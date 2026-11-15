# Proof tactics

This page is the reference inventory of the tactics in Click's specification
language. A tactic is either **smart**, **simple**, or **control**:

- Smart tactics search. The written one is `solve()`, with its `using` form
  and `step_until`, which steps to a target and proves what each step needs;
  the rest are the implicit closer that ends every proof, including each loop
  `preserve` script at its back edge, and finishes a `step()` or `fold`, and
  the elided forms whose search fills one argument a simple form writes:
  `apply(theorem(args))`, `apply(ih(m))`, and a bare `transport(P, Q)`. They
  are the tactics that `click profile` may recommend expanding. The parser
  refuses the removed spellings `auto()`, `arithmetic()`,
  `execute()` and `execute_until` and names each replacement.
- Simple tactics request one deterministic checked operation without heuristic
  planning or search. They may use indexed ambient context when that context is
  an input to the operation, as it is for `step()`. They are the leaves emitted
  by `click expand` and must be fast and output-sensitive: their work may scale
  with relevant input and produced state, but not unrelated ambient state.
- Control tactics contain, scope, split, or join proof scripts. Their descendants, not
  the container itself, determine whether an expanded proof is simple.

[Smart and simple tactics](../../concepts/smart-and-simple-tactics.md) is the
canonical definition of these classes.

Each simple tactic's section states what it **accepts**, a guarantee, and what
is **outside it**, with what to write instead. A simple tactic that refuses a
case its Accepts list covers is a Click bug; one that refuses a case outside
the list is working as documented. Behavior a section describes as beyond the
list is not guaranteed. [Tracing](../../concepts/tracing.md) uses this
distinction for its `failing-tactic` outcome.

## Core tactics

A handwritten proof needs about fifteen tactic words. The tables below are
lookup indexes: each form has a class, an audience, a short purpose, and a
link to its detailed rules and checked examples.

The audience is **Core** for the forms listed here, **Specialized** for a
handwritten tactic used in a narrower situation, or **Expansion output** for
a form usually written by `click expand`. These categories describe usage
in the checked examples, mdtests, and expansion output. Every listed form
remains supported.

- Nothing: a proof that stops with C left runs the rest, splitting at
  undecided C `if`s and open Rust enum `match`es, and closes every goal on
  every path. See [Automation and search](#automation-and-search).
- `step()`: run one C statement, to put proof steps between statements. See
  [Execution](#execution).
- `step_until(target)`: run to one statement, loop, or `function.exit`
  without splitting. See [Execution](#execution).
- `branch { ... } else { ... }`: prove each arm of the C `if` at the
  frontier. See [Execution](#execution).
- `loop { ... }`: prove a C loop from its invariants, which the back edge
  closes member by member with `solve()`. See [Execution](#execution) and
  [Resources and transport](#resources-and-transport).
- `solve()`: close the first open goal, and `solve() using { ... }` from only
  the listed premises. See [Automation and search](#automation-and-search)
  for the different proof-clause forms and their defaults.
- `have P by ...`: prove an intermediate fact and add it to the context. See
  [Proposition reasoning](#proposition-reasoning).
- `apply(theorem(args))`: use a verified theorem, proving its premises. See
  [Proposition reasoning](#proposition-reasoning).
- `unfold(...)`: open one layer of a pure function, a predicate, or an owned
  resource. See [Proposition reasoning](#proposition-reasoning) and
  [Resources and transport](#resources-and-transport).
- `fold(resource)`: close an owned resource from its body. See
  [Resources and transport](#resources-and-transport).
- `if P { ... } else { ... }`: split the proof on a proposition you choose.
  See [Proposition reasoning](#proposition-reasoning).
- `match value { ... }`: split the proof on an algebraic value's
  constructors. See [Proposition reasoning](#proposition-reasoning).
- `intro()`: assume an implication's antecedent or fix a universal's
  variable. See [Proposition reasoning](#proposition-reasoning).
- `induct(n) as ih` or `induct(xs) as ih { ... }`, with `apply(ih(m))`: prove
  a pure theorem by induction. See
  [Proposition reasoning](#proposition-reasoning).
- `rewrite(from, to)`: rewrite the goal with an available equality. See
  [Proposition reasoning](#proposition-reasoning).
- `contradiction(P)`: close an impossible case from a fact and its negation.
  See [Proposition reasoning](#proposition-reasoning).

## Which to use

Several tactics overlap. Start with the default, and reach for another only
when the default misses or when a proof must not search.

- **Running C.** Stopping is the default: the C a script leaves is run by
  the implicit tail that ends every proof. Write `step()` lines where proof
  steps must come between statements, and `step_until(...)` to run to one
  point, `function.exit` included, without splitting. `branch` and `loop`
  are what the tail does at a C `if` or loop, written out to state what each
  arm or iteration proves; a proof `if` before the C splits the paths that
  return differently, each arm stepping to exit.
- **Closing a proposition: `solve`, `known`, `normalize`,
  `arithmetic_certificate`, `extract`.** Letting the script end, so that the
  implicit closer closes the goal, is the default, and `solve()` closes the
  first open goal where a script continues after it. Write
  `solve() using { ... }` for a goal that follows from named facts, an
  integer bound or equality among them: it tries arithmetic over the listed
  premises last. `known()`
  (the goal is an available fact), `normalize()` (the goal is true by
  evaluation) and `extract(P)` (one part of a fact) do no search. They are
  what expansion writes; write them by hand only in a proof that must not
  search.
- **Equalities and states: `rewrite`, `transport`.** `rewrite(from, to)` is the
  default: it rewrites the goal with an equality at the current state.
  `transport(P, Q)` carries a fact stated at an earlier state to the current
  one when `step` did not carry it; its `using` form, which lists the frame
  evidence, is expansion output. `solve` tries both within its bounds.
  A full pointer-value equality also rewrites displaced copies such as `p + i`,
  retaining their selected bounds. An equality of `address(p)` and `address(q)`
  supplies numeric addresses without transferring object identity or bounds.
  A frame refusal prints both written operands and the checked propositions,
  followed by the frontier effects and a shared memory/value legend. The
  checked propositions may simplify to `true` or `false`; those are the
  terms the checker compared. With `--trace-proof`, a rejected written
  transport retains the preceding checked path without admitting its target. A planning
  budget failure retains that prefix too; if source and target were already
  lowered, it prints their checked identities and memory legend without
  running more proof checks.
- **Case splits: `if`, `cases`, `match`, `branch`.** `if P` splits on any
  proposition; `cases` uses a disjunction that is already a fact; `match`
  splits on constructors; `branch` follows a C `if`. Tactics written after a
  proof `if`, `cases` or `match` are checked once, never once per arm: the arms rejoin,
  keeping the facts every arm proved, or the split is refused. An arm that
  reaches function exit is a finished path, like each `return` of the C: the
  implicit closer that ends the proof closes its remaining goals on that
  path, so a split that ends a proof finishes each arm on its own.

## Automation and search

Every proof script ends with an implicit tail, and an omitted proof clause is
that tail alone. The tail runs the C the script leaves, splitting at each C
branch the facts do not decide into paths that each run to function exit,
and then closes every open claim on every path with the implicit closer, per
claim or once for a grouped proof. A written `solve()` closes the first open goal and runs no C, so
`by solve();` restates the omitted proof only where no C is left to run, as
for a pure theorem or a `have`; with C left it is refused, since its goals
exist only at function exit. The implicit closer tries direct logical closure on each open claim,
then `solve`'s search. On a
returned path that holds the body of a resource the contract produces but
not the resource, it first folds it, as a written `fold(R(...))` after the C
would; a fold that does not check leaves the path as it was
(`mdtests/an_omitted_proof_folds_the_resource_its_contract_produces.md`). A proof
script that ends with a claim still open closes it the same way, so a script
needs no final closer and no final step to function exit. The body of an `open` scope is
the exception: the scope closes where its body ends, before the tail runs, so
a body that must reach the function's return steps there itself with
`step_until(function.exit)`. On a stated fact,
`have P by solve();`, there is no C to execute.

On an arithmetic goal that its indexed derivations miss, `solve` runs
arithmetic from premises it selects itself: the facts connected to the goal,
and the type ranges of the machine values they observe. It also carries
connected machine orders to `Integer`, proves a machine order through its
`Integer` reading, an equality from its two bounds, and `defined(a + b)` from
the bounds of the exact result (see
[intermediate facts](#intermediate-facts)). A loop bundle member, which may
cite only the loop head and the contract, selects nothing. When its other
strategies miss, `solve` works from the facts connected to the goal. It reads a condition a function
fact forces out of the function's definition
(`mdtests/solve_reads_a_condition_out_of_a_definition.md`), then rewrites the
goal by the connected equalities: first a goal that
restates an available fact through one connected equality, such as
`f(Node(..)) == 1` beside `f(t) == 1` and `t == Node(..)`, by one `rewrite`
and `known` (at most 16 rewrites), then a bounded chain of up to three
rewrites whose rewritten goals the direct closers and a nested `solve` try.
Last, it states the equation between two constructor applications that facts
equate to one value, and reads the fields' equalities, or the constructors'
mismatch, from it
(`mdtests/solve_reads_definitions_and_constructor_equations.md`).
Written
as a step of a script, `solve();` closes the first open goal
(`mdtests/a_written_solve_closes_one_goal.md`). A
script that stops with C left ends with the implicit tail, which executes
whatever remains and closes every open goal
(`mdtests/a_script_that_stops_after_explicit_steps_executes_the_rest.md`). In
each arm of a proof `if` that ends a proof, the arm's own closer closes that
arm's goals
(`mdtests/solve_closes_each_arm_of_a_split_that_ends_a_proof.md`). Successful smart tactics and the implicit closer retain the checked
surface provenance that `click expand` can render as an explicit proof.
Source-premise selection skips synthesized candidates whose rendered
propositions do not tokenize as Click, rather than counting a route through an
unnamed kernel value as a successful expandable proof.

When the implicit tail executes a C store or read that is
refused because the place lies inside a folded resource the frontier owns,
it unfolds the one owned resource whose body holds that place and retries
the operation, one layer per refused access. It never chooses between
resources: when no owned resource's body holds the place, or more than one
does, the refusal stands. Expansion writes each opening as an explicit
`unfold(...)`. The contract's resource transition folds the resource again
at function exit. A written `step()` never opens a resource. See
[`implicit_tail_opens_a_folded_resource_to_store_through_it.md`](https://github.com/clicklang/click/blob/master/mdtests/implicit_tail_opens_a_folded_resource_to_store_through_it.md)
and
[`a_written_step_does_not_open_a_folded_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/a_written_step_does_not_open_a_folded_resource.md).

A C store into an array keeps a cached element of that array only on a
stated disequality of the two index words, compared as `int32`, or as
`uint64` or `int64` for two 64-bit indices of that signedness such as
`size_t` ones (see [Verifier design](../../internals/verifier-design.md));
otherwise it drops the element. When a statement the implicit tail or
`step_until` runs drops such an element, the tail spells that disequality
from the two index words, `((m - 1) as int32) != 0`,
`((n - 1u64) as uint64) != 0u64` or `j != 0u64` say,
proves it at the statement's pre-state, retains it as a `have`,
and runs the statement again, which then keeps the element. It tries at most
four dropped elements per statement, and proves each only by the signed
interval certificate over its variables' bounds, an order between the two
indices by selected-premise arithmetic, or the disequality bridge of
[`solve`'s arithmetic](#arithmetic-with-selected-premises) (a case split on the index
equality), not by the rest of `solve`. Bounds such as `2 <= m` or `1 <= j`,
`1 <= m` with `m != 1` (a bound made strict by a disequality of its own
difference,
[`a_store_index_bound_and_disequality_keep_a_cached_element.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_index_bound_and_disequality_keep_a_cached_element.md)),
or the Integer fact `m - 1 != 0` where `m - 1` cannot wrap, suffice. Expansion writes the `have` before the
statement's `step()`. A disequality it misses leaves the statement as it
ran. The path keeps the miss (at most 32 per path): a later refusal whose
goal reads the dropped element names the statement and the disequality the
tail spelled, ``statement(3) may have overwritten `q[0]`; it is kept if you
state `have … by { ... };` before statement(3)``, and `--trace-proof` marks
the store that dropped it
([`a_store_search_miss_names_the_store_and_the_fact_for_a_heap_read.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_search_miss_names_the_store_and_the_fact_for_a_heap_read.md),
[`a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.md),
[`a_stated_store_search_fact_keeps_the_heap_cell.md`](https://github.com/clicklang/click/blob/master/mdtests/a_stated_store_search_fact_keeps_the_heap_cell.md),
[`a_store_at_the_last_heap_element_keeps_the_first.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_at_the_last_heap_element_keeps_the_first.md),
[`a_store_at_another_symbolic_element_keeps_a_cached_one.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_at_another_symbolic_element_keeps_a_cached_one.md),
[`a_store_at_an_index_that_may_be_the_cached_one_overwrites_it.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_at_an_index_that_may_be_the_cached_one_overwrites_it.md)).
`size_t` and `long` indices work the same way
([`a_store_at_the_last_size_t_heap_element_keeps_the_first.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_at_the_last_size_t_heap_element_keeps_the_first.md),
[`a_size_t_store_index_fact_variants_keep_the_first.md`](https://github.com/clicklang/click/blob/master/mdtests/a_size_t_store_index_fact_variants_keep_the_first.md),
[`a_size_t_store_search_miss_names_the_word_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/a_size_t_store_search_miss_names_the_word_fact.md),
[`a_stated_size_t_store_search_fact_keeps_the_heap_cell.md`](https://github.com/clicklang/click/blob/master/mdtests/a_stated_size_t_store_search_fact_keeps_the_heap_cell.md),
[`a_size_t_store_at_an_index_that_may_be_the_cached_one_overwrites_it.md`](https://github.com/clicklang/click/blob/master/mdtests/a_size_t_store_at_an_index_that_may_be_the_cached_one_overwrites_it.md),
[`a_wrapping_size_t_store_index_overwrites_the_cached_element.md`](https://github.com/clicklang/click/blob/master/mdtests/a_wrapping_size_t_store_index_overwrites_the_cached_element.md)).
A pair of a 32-bit and a 64-bit index, or of two 64-bit indices of different
signedness, has no index fact the store reads, and the store drops the
element.

A failed `have P` that the implicit closer proves names the written `P`,
rather than an internal search step or subgoal. Exhausted verification
budgets keep their budget diagnostic. See
[`solve_failure_names_the_written_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_failure_names_the_written_goal.md).

The implicit closer reads a goal that is one of a function's `if` conditions out of a
connected fact `f(args) == k`, with `k` an integer constant: the arguments
pick the definition's `match` arms, and when every way through its `if`s
that fails the goal's condition ends in a constant other than `k`, the fact
forces the goal, as `is_rb(Node(.., left, right)) == 1` forces
`is_rb(left) == 1`. An argument that a connected equation names as a constructor,
such as a `match` arm's `up.model == Context::Left(..)`, is replaced by it:
the fact is first restated as a `have` by rewriting with that equation. The proof is ordinary checked steps: `if` the goal
holds, `known`; otherwise a proof `if` on each condition met before the
goal's, and at each end `have f(args) != k` by `unfold` and
`normalize() using` the conditions taken, then `contradiction`. At most 16
connected function facts are read, each up to 16 ends; a `match` that its
arguments do not decide, or an end that is not a constant, is a miss. See
[`solve_reads_a_condition_out_of_a_definition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_reads_a_condition_out_of_a_definition.md)
and
[`solve_does_not_read_an_unforced_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_read_an_unforced_condition.md).
The function may be generic, and `bool`-valued with `true`/`false` ends: the
fact `list::contains(xs, x)` reads as `== true`, and is refuted by
`have not list::contains(xs, x)`. An end that applies a defined function, as
`list::contains(Nil, x)`, is followed into that definition (at most 4 deep)
and unfolded after the fact's own application. A condition spelled other than
the goal, `v == x` against a postcondition's `result == x`, matches when it
lowers to the same goal. So `list::contains(Cons(v, Nil), x)` forces `v == x`
([`solve_reads_a_condition_out_of_a_generic_bool_definition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_reads_a_condition_out_of_a_generic_bool_definition.md),
[`solve_does_not_read_an_unforced_generic_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_read_an_unforced_generic_condition.md)).

Signed `int32` arithmetic substitutes equalities: `x == 5` bounds `x` on
both sides, so it proves `x - 1` defined and closes `x - 1 == 4`; a listed
`a == b + 1` with `b` bounded converts to `a - b == 1` and bounds `a`, and
`c == a + 1` converts after it. A bound substitutes through such equalities
in turn to the listed bounds on what remains. `solve` gathers a goal
variable's equalities beside its bounds when the bounds alone decide
nothing, so a callee's `ensures o.size == old(o.size) + delta`, about a
resource field or a cell, supports arithmetic across calls (see
[`arithmetic_using_chains_equalities.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_using_chains_equalities.md)
and
[`abstract_resource_field_call_facts_support_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/abstract_resource_field_call_facts_support_arithmetic.md)).

For a signed `int32` bound, `solve` can use an indexed equality of a goal
operand to a literal even when that call-derived equality has no recorded
source spelling. It first proves the equality in a checked nested `have`
using the operand as written in the goal, then rewrites and closes the bound.
False bounds and equalities invalidated by a later store remain refused; see
[`post_call_constant_equality_proves_a_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/post_call_constant_equality_proves_a_bound.md).

Refused call prerequisites name the callee and the original required-clause
position, including clauses already discharged. Statement-step diagnostics
use the written tactic position in the current block, counting preceding
`have` steps. See
[`call_prerequisite_names_the_second_source_clause.md`](https://github.com/clicklang/click/blob/master/mdtests/call_prerequisite_names_the_second_source_clause.md)
and its first-clause companion.

For ordinary authoring, start with the omitted proof, or the
smallest comprehensible smart tactic. Use `click profile` before replacing a
smart tactic with an exact explicit proof. The simple forms below are public,
maintained Surface Click, but long `using` blocks are normally expansion output
rather than a recommended first draft.

When a call's generated pointer has no source struct layout, expansion spells
an indexed array field as an explicit typed read at its byte address. This
retains the field offset and element width when reparsed; it grants no read
authority. Named struct pointers and library model accessors retain their
ordinary spelling. The Rust
assignment-operator audit checks this through an erased local array pointer.

For equality of a 32-bit or 64-bit machine integer with a literal, `solve` and
the implicit closer stop searching when current facts already decide the opposite truth
value. An inconsistent context remains eligible for contradiction closure.
The reference-call scaling regression compares valid results with false
literal results over four sizes; refusal does not spell every old call fact.

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
smaller execution steps or exact premises; `solve() using { ... }` constrains
pure search to named facts, while a shorter run of `step();` lines isolates
the one execution transition that fails.

## Execution

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `mark name;` | simple | Specialized | Name the current execution state. | [Reference](#proof-marks) |
| `step()` | simple | Core | Execute one checked statement transition. | [Reference](#single-statements) |
| `let { result: name } = step()` | simple | Specialized | Bind the checked value of a scalar assignment. | [Reference](#binding-a-statement-result) |
| `step_until(statement(i))` | smart | Specialized | Execute up to a selected source point, or to `function.exit`, without splitting. | [Reference](#execution-to-a-point) |
| `branch [ensuring { ... } then] { ... } else { ... }` | control | Core | Prove and join the arms of source control flow. | [Reference](#source-branches) |
| `loop [as name] { ... }` | control | Core | Prove a loop from its invariants and ranking obligations. | [Reference](#loop-transitions) |
| `step(Contract)` | simple | Specialized | Select a named contract for a call. | [Reference](#calls-through-named-contracts) |
| `step(callee, { binder: instance })` | simple | Specialized | Map a call's instance binders and value parameters, and name what it produces. | [Reference](#calls-with-binder-maps) |
| `step(Contract, { handle: instance, ... })`; `step(Contract, { binder: instance })` | simple | Specialized | Select a contract and map its resource instances. | [Reference](#named-contracts-with-resource-bindings) |
| `step(...) by { ... }` | control | Expansion output | Supply an explicit proof for one open obligation. | [Reference](#one-statement-obligation) |
| `step(...) { requires P by ...; }` | control | Expansion output | Supply proofs for selected open obligations. | [Reference](#several-statement-obligations) |

The boundaries are intentional: `step` is one concrete transition, `branch`
and `loop` unpack the corresponding C control flow at the current frontier,
`loop` constructs and applies one verified abstract loop transition,
`step_until` repeats transitions to a point, and the implicit tail runs
what a script leaves to function exit. A branch continuation executes once
after its arm states have joined.

Marks are local to one proof and their names cannot be rebound. They remember
an already-reached state; they are not source labels, execution targets, or
saved states that can be restored. In particular, `step_until(name)` does
not target a proof mark.

Expansion of execution automation emits one `step();` line per executed
statement, followed by the outcome closers. Expansion recurses through `loop` and materializes omitted
phase proofs at the loop keyword. The older numbered-loop summary syntax
remains migration compatibility and should not be used in new proofs.

### Proof marks

**Form:** `mark name;`

**Specialized.** Write it to name the current state so a later fact can refer to
it with `at(name, ...)`. At any live execution frontier, give the point the
path is at now a proof-local name without advancing C.

**Accepts** a name not yet marked on the current path, at a live frontier of a
C function's execution script: the claim's top-level script, a `branch` arm, a
proof `if` or `cases` arm, or a loop's `preserve` proof. It records the current
state under that name and changes nothing else:

- From then on `at(name, e)` reads `e` in the recorded state. It can appear in
  a `have`, a `branch ensuring` interface, or the `ensures` clause the script
  proves (`ensures result == at(after_first_write, x) + 1 by { ... }`).
- The name stays visible after later steps and after a `branch` join, and
  inside nested loop `preserve` proofs.
- The two arms of one `branch` or proof `if` may each mark the same name.

**Outside it**, with what to write instead:

- A name already marked on this path fails with `duplicate proof mark`. Choose
  another name.
- A name that is not yet marked, used in `at(name, ...)` before its `mark` or
  never marked, fails with `unknown proof mark`. Put the `mark` where the proof
  reaches that state.
- A mark made inside a `preserve` proof, read outside that proof, also fails
  with `unknown proof mark`. Loop invariants use `at(loop(n).entry, e)`.
- At function exit (after the last `step()` or `step_until(function.exit)`), `mark` is refused.
  Mark before the last step, or name the final values directly.
- Inside a `have ... by { ... }` body or a pure theorem, `mark` is refused.
  Write the mark in the execution script.
- A mark names a point the path has already reached, not a point in the C
  region tree that execution can be sent to. `step_until(name)` does not target
  a mark; use `step_until(statement(i))`.

**Failure, checking, and tools:**

Click records the exact state at the marked point. Expansion leaves the simple tactic
unchanged, and profiling attributes only its bounded checking work.

**Checked examples:** [`proof_mark_current_frontier.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_mark_current_frontier.md), [`proof_mark_duplicate.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_mark_duplicate.md), [`proof_mark_unknown.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_mark_unknown.md), [`proof_mark_survives_branch_join.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_mark_survives_branch_join.md), [`nested_loop_enclosing_mark.md`](https://github.com/clicklang/click/blob/master/mdtests/nested_loop_enclosing_mark.md), [`nested_loop_inner_mark_stays_local.md`](https://github.com/clicklang/click/blob/master/mdtests/nested_loop_inner_mark_stays_local.md)

### Single statements

**Form:** `step()`

**Core.** At a live C frontier, execute the next statement with every fact in
the proof context visible to the kernel. At a C `if`, an available condition
fact selects and enters one arm; at a loop head, it evaluates the condition once
and enters one iteration or advances past the loop.

**Accepts** the next lowered C statement at a live frontier of a function
proof, when that statement has exactly one feasible successor in the proof
context. One `step()` executes exactly one of these:

- An expression statement, an assignment (including `x += e` and `x++`), a
  call statement `g(x);` or call assignment `y = g(x);`, a declaration
  without initializer, an empty statement, `return`, `break`, `continue`, or
  `goto`. An empty block `{ }` or an omitted `else` is one step, and so is the
  end of a `void` body. The braces of a non-empty block are not a step.
- A declaration with an initializer, `int32 y = e;`, is two steps: the
  declaration, then the initializing assignment.
- A call nested in a larger expression is a step of its own before the
  statement that uses its value: `return g(x);` is two steps, and
  `if (g(x) > 1)` is the call and then the `if`.
- A checked global-array index adds an `assert` step before the access: in
  `r = values[x];` the first step checks the bound and the second step loads.
- A call to a `static inline` helper that has no Click contract runs the whole
  helper body in one step.
- At a C `if`, one step evaluates the condition and enters the arm the context
  decides. The arm's statements follow, and leaving the arm is not a step.
- At a loop head (a `while` condition, a `for` condition, a `do ... while`
  condition), one step evaluates the condition and enters the body or
  advances past the loop. A `for` initializer and increment are one step each,
  the first entry into a `do` body is one step, and the back edge is not a
  step.
- A `switch` whose selector the context decides runs as one step through the
  selected case to its `break`.

The diagnostic `the frontier is at statement N, ...` names the next statement,
and `click expand` on the implicit tail prints one `step` per statement,
with explicit prerequisite proofs where needed.

The context decides a condition when the kernel refutes the other path from
the facts. It uses exact facts, the conjuncts of an `and` fact, the condition
of the enclosing proof `if` or `cases` arm, constants and assigned values, and
linear bounds it combines: `x > y` and `y > 3` decide `x > 3`, and
`x > 10` and `x < 100` decide `x * 2 > 3`.

Call preconditions and emitted verification conditions become obligations at the
step's pre-state. Each obligation is proved by a written `step() by { ... }`
body or ordinary implicit `solve()`, even if the fact is already available.
An exact known precondition normally expands to `step() by { known(); }`.
This solving is smart and may miss; for example, it can prove a callee's
`requires a > 0` from `requires x == 5 or x == 7`.

Arithmetic evaluation still decides some safety conditions before generating
an obligation; migrating those decisions is separate remaining work. An emitted
definedness requirement states the defined path's condition, such as
`s >= 0 and s < 32` for `x << s`.

The step produces one successor state:

- Assigned locals and stored cells hold the evaluated values. After
  `y = x + 1;`, `have y == x + 1 by known();` closes.
- A call adds the callee's `ensures`, instantiated at the call's arguments and
  result, and applies its ownership transition.
- A fact keeps the meaning it had. A fact about an entry value stays about
  that value: after `x = 0;`, `old(x) > 5` still holds and `x > 5` is false.
  A fact about a cell the context proves unwritten keeps that cell's name, so
  `p[0] == 7` survives a store to `p[1]` or to `p[i]` with `i == 1`.
- An `if` that the context decides adds no condition fact. A proved `assert`
  condition prunes the false path.

**Outside it**, with what to write instead:

- A statement with two or more feasible successors. That is an undecided `if`
  or loop head; an assigned comparison whose value is not decided
  (`b = x > 3;`); a short-circuit condition; a symbolic `switch`; a load that
  may read an earlier store; an open Rust enum `match`; or a maybe-throwing
  call. The refusal names each successor's condition. Use `branch`, a proof
  `if` or `cases` on that condition, a proof `match`, or `outcomes { ... }`, or
  stop the script and let the implicit tail split it.
- A branch condition the kernel does not decide, because it needs a
  disjunction, an implication, a folded predicate, or a quantifier: state it
  first with `have`, `unfold` the predicate, or split with a proof `if` or
  `cases`. A requirement the implicit closer misses: prove the printed `goal:`
  with `have` before the step or in `step() by { ... }`.
- A call whose callee declares instance binders while the caller holds more
  than one candidate instance: use `step(callee, { binder: instance })`.
  A call through a pointer with two applicable contracts that carry resources:
  use `step(Contract)`. A named contract with resource binders: use
  `step(Contract, { ... })`.
- An access through a resource held folded: `unfold` it first. A step never
  opens or closes a resource.
- At function exit (`cannot run after execution already reached function
  exit`), or inside a `have` body or a pure theorem: close the goals, or move
  the step into the execution script.
- Running several statements: use `step_until(...)`, or stop the script.

When the caller holds exactly one instance of a binder's resource, a plain
`step()` binds the binder to that instance. Also, `return x > 3;` executes
without the split that `b = x > 3;` needs. Neither behavior is guaranteed, so
a refusal there is not a bug.

**Failure, checking, and tools:**

A prerequisite the context cannot prove, or an unsupported transition, fails at
that statement with that diagnostic. A refusal printed as `refused
by: the implicit closer that proves this statement's requirements` is a smart
miss. Prove
the printed `goal:` with `have` before the step, or prove it with
`step() by { ... }`. When the implicit closer cannot spell or prove an obligation, the
step is refused at that obligation. Requirement generation does not invoke
proof search; the driver runs the implicit closer.

An `assert`'s false-path obligation (as a Rust overflow check lowers to) is
spelled as the asserted condition at the pre-state, less any disjunct an exact
fact refutes.

Click carries no fact by list. Expansion leaves a step unchanged unless the
implicit closer proved an obligation. Then it prints `step() by { ... }` for
one obligation or `step() { requires P by ...; }` for several. Profiling
charges the step its one transition, and the implicit closer's work is a
separate smart `implicit closer` row at the step.

**Checked examples:** [`simple_statement_step.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step.md), [`simple_statement_step_branch_requires_exact_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_branch_requires_exact_fact.md), [`simple_statement_step_requires_exact_prerequisite.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_requires_exact_prerequisite.md), [`step_refuses_an_undecided_c_if.md`](https://github.com/clicklang/click/blob/master/mdtests/step_refuses_an_undecided_c_if.md), [`step_names_the_alias_cases_it_does_not_split.md`](https://github.com/clicklang/click/blob/master/mdtests/step_names_the_alias_cases_it_does_not_split.md), [`step_refuses_a_maybe_throwing_call.md`](https://github.com/clicklang/click/blob/master/mdtests/step_refuses_a_maybe_throwing_call.md), [`step_by_proves_its_one_open_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/step_by_proves_its_one_open_obligation.md), [`a_written_step_does_not_open_a_folded_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/a_written_step_does_not_open_a_folded_resource.md), [`smart_step_carries_prior_call_facts.md`](https://github.com/clicklang/click/blob/master/mdtests/smart_step_carries_prior_call_facts.md)

### Binding a statement result

**Form:** `let { result: name } = step()`

**Specialized.** Write it when a later fact must name an assigned value after
its local is overwritten or leaves scope. Execute the scalar assignment at the
current frontier and bind its checked value to an immutable proof name. The name
continues to denote that value after the source local is overwritten or leaves
scope.

**Accepts** a frontier whose next lowered statement assigns a scalar or
pointer C local without a call: `y = e;`, `x += e;`, `x++;`, or the second
step of `int32 y = e;` (its initializing assignment). `name` must not be a C
local in scope or a parameter. A proof name may be bound again, and the newest
binding wins. The step executes exactly as `step()` does, and `name` then
denotes the assigned value.

**Outside it**, with what to write instead:

- An assignment from a call, `y = g(x);`: use
  `let { result: name } = step(g, { })`. The empty map is enough for a
  callee without binders.
- A store through a pointer, field, or array element (`p[0] = 3;`,
  `p->v = 3;`): use `step()` and name the cell.
- A `return`, a declaration's first step, or any other non-assignment: use
  `step()`. `result` names a returned value.
- A name that is a C variable here is refused with `names a C variable here`.
  Choose another name.
- An output other than `result`, such as `let { value: v } = step()`, is
  refused with `has only the result output`.

**Failure, checking, and tools:**

The ordinary step checks every access and arithmetic prerequisite, and the
binding adds no assumption. Expansion retains the binding unchanged.

**Checked examples:** [`step_result_binding_names_checked_values_and_survives_overwrite`](https://github.com/clicklang/click/blob/master/src/surface/tests/project_tests.rs), [`a_step_result_name_can_be_bound_again.md`](https://github.com/clicklang/click/blob/master/mdtests/a_step_result_name_can_be_bound_again.md), [`step_result_binding_refuses_a_store_through_a_pointer.md`](https://github.com/clicklang/click/blob/master/mdtests/step_result_binding_refuses_a_store_through_a_pointer.md)

### Execution to function exit

**Form:** none; the implicit tail. The parser refuses the removed spelling
`execute()` and names the implicit tail and `step_until(function.exit)`.

**Core.** A proof that stops at a live frontier runs to function exit on the
checked proof: one `step()` per statement, a `branch` at each undecided C `if`
or call outcome, and
a proof-level case split where a condition or statement needs explicit path
selectors (a short-circuit, a symbolic `switch`, a may-alias load), and a
proof `match` at a Rust enum `match` whose variant is open, binding each
field as `<local>_<variant>_<index>` ([Rust enums](../rust.md#enums-and-match)).

A loop the context decides is walked one iteration at a time, within a
10,000-step budget. Each arm of a `branch` runs to function exit, so `n`
sequential C branches give `2^n` paths; past 1,024 splits the tail stops and
names the join to write instead: a `branch ensuring { ... }` at each C `if`
([`sequential_branches_join_with_branch_ensuring.md`](https://github.com/clicklang/click/blob/master/mdtests/sequential_branches_join_with_branch_ensuring.md)),
or a proof `if <condition> ensuring { ... }` at a condition inside a
statement, such as `?:`.

**Failure, checking, and tools:**

The first statement that cannot run in the whole proof context fails the proof
with that step's diagnostic, and no partial result is kept. Expansion emits the
explicit steps, splits, and branches, and profiling attributes them to a site
after the script's last written tactic. Automatic path selectors must re-lower to the exact checked condition;
their native load widths and short-circuit operand facts are preserved.

When one arm of a `branch` returns, the rest of the script runs in the arm that
continues, and a script that stops there is finished by the tail too
(`mdtests/a_script_that_stops_in_the_arm_that_continues_runs_the_rest.md`).
A `step()` that runs past the end of an arm that must stop at its shared
continuation is refused and names that arm limit.

To run to function exit and do proof work there on one path, write
`step_until(function.exit)` and then the work; it never splits, and at a
branch the facts do not decide it names the split to write
([Execution to a point](#execution-to-a-point)).

**Checked examples:** [`execute_branch_arm_stops_at_shared_continuation.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_branch_arm_stops_at_shared_continuation.md), [`tactic_execute.md`](https://github.com/clicklang/click/blob/master/mdtests/tactic_execute.md)

### Goals after execution

When execution reaches function exit, the path's open goals are the
contract's claims in the order the contract writes them: every `ensures`, and
every `owns` and `produces` clause, whose goal is that the path still holds the
instance. `views` and `consumes` clauses make no claim. A closer (`known`,
`normalize`, `both`, `solve`, `solve() using`) acts on the first
open goal, and a refusal names that goal; it does not look further down the
list for a claim it could close
(`mdtests/a_closer_after_execution_acts_on_the_first_open_claim.md`,
`mdtests/solve_after_execution_acts_on_the_first_open_claim.md`). The implicit
closer is the catch-all: it closes every goal still open.
`known()` closes a resource goal whose instance the path holds
(`mdtests/closers_after_execution_close_a_resource_goal_first.md`). A closer
written when every goal on the path is closed is refused
(`mdtests/a_closer_with_no_open_goal_is_refused.md`). `fold`, `apply`, `have`
and the other tactics that change the path's facts or resources act on the path
and leave the goal list alone; the implicit closer at the end of the script
closes the goals still open.

Some tactics leave a claim on its own proof, which later closers continue
instead of the claim. `choose`, `witness`, `let` and `intro` open the proof of
the first open proposition claim, and `rewrite` rewrites each open claim on
its own proof. Before a tactic continues such a proof, the proof takes up the
path's current state and resources, so a later `fold` or the contract's
resource transition reaches it. A `have` written after `intro` extends that
proof. A closer that does not apply to a proof that `intro` opened is read
against the goal list instead. A closer that does not apply to a proof only
`choose`, `witness` or `let` opened is an error, since closing the claim
another way would drop the witness.

A written closer that closes no goal it acts on is refused, `solve` and
`solve() using` included; only the implicit closer at the end of the script
leaves an open claim to the report that names it
(`mdtests/a_written_solve_that_closes_nothing_is_refused.md`).

### Execution to a point

**Form:** `step_until(statement(i))`

`step_until` repeats `step()` up to the target, walking any loop the facts
decide, and never splits: an undecided branch before the target refuses it, as
it refuses `step()`. The parser refuses the removed spelling `execute_until`
and names `step_until`.

**Specialized.** Write it to stop execution at a chosen statement, loop, or read
and do proof work there, instead of a run of `step();` lines. From a live
frontier, execute forward to the selected region's entry without creating a
proof interface. Any statement region names a target:
`step_until(statement(i).statement(j))` stops before a nested statement and
`step_until(statement(i).call(f, j))` stops just before one of its calls
(`mdtests/step_until_runs_to_a_statement_region.md`);
`.assignment(x, j)` and `.read(j)` end a chain the same way, at the
statement's `j`th own store to `x` or memory load
(`mdtests/a_chained_region_ends_in_an_assignment_or_read.md`).
An ordinary scalar C call assignment has a call-result step followed by an
assignment step. A C aggregate call with a declared return type similarly has
a call-result step followed by a destination-copy step. Their `.call(...).exit`
and `.assignment(...).exit` name distinct points, even when both effects come
from one C statement (`mdtests/aggregate_call_and_destination_copy_have_separate_points.md`).
`step_until(region(N))` stops before the `N`th atomic region;
`step_until(loop(N))` selects the indexed loop entry;
`step_until(assignment(local, N))` selects the Nth static local assignment
of the function before it executes.

`step_until(read(N))` stops before the Nth statement of the function
containing an explicit scalar memory read. `step_until(back_edge())`
finishes the current loop preservation region with checked steps; invariant
and ranking closure are separate. `step_until(loop(i).back_edge())` does the
same and is refused outside `loop(i)`'s preservation region
(`mdtests/step_until_refuses_another_loop_s_back_edge.md`).

`step_until(function.exit)` steps until the function returns, and the proof
continues at exit, where `result` names the returned value. Where the C
reaches an `if` the facts do not decide, it is refused and names the split
to write there: `branch` at the C `if`, or a proof `if` in front of the C,
each arm stepping to exit on its own path
(`mdtests/step_until_steps_to_function_exit.md`,
`mdtests/step_until_runs_inside_a_branch_arm.md`,
`mdtests/step_until_function_exit_refuses_an_undecided_branch.md`).

**Failure, checking, and tools:**

A missing, backward, unreachable, or branch-hidden target fails, and so does
a statement target once execution has reached function exit.
The indexed source layout resolves loop entries. Click checks every crossed
transition; expansion prints those steps, and profiling reports the selected
site.

**Checked examples:** [`step_until_runs_to_a_statement_region.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_runs_to_a_statement_region.md), [`step_until_current_frontier.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_current_frontier.md), [`step_until_selects_loop_entry.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_selects_loop_entry.md), [`step_until_assignment.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_assignment.md), [`step_until_read.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_read.md), [`step_until_back_edge.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_back_edge.md), [`step_until_back_edge_of_a_named_loop.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_back_edge_of_a_named_loop.md), [`a_chained_region_ends_in_an_assignment_or_read.md`](https://github.com/clicklang/click/blob/master/mdtests/a_chained_region_ends_in_an_assignment_or_read.md), [`step_until_steps_to_function_exit.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_steps_to_function_exit.md)

### Source branches

**Form:** `branch [ensuring { ... } then] { ... } else { ... }`

A plain `branch` starts its first arm directly with `{`. With an `ensuring`
interface, `then` separates that interface from the first arm. The same rule
applies to a proof `if`; `then` is required with the interface and refused
without it.

**Core.** At a C `if` frontier, prove every feasible arm and join nonreturning
arms into one continuation. Arms that end in one state join as they are. Arms
that end in different states join keeping what both agree on: a local or cell
both arms hold with the same value, and the resources both still own; what only
one arm established is gone, and a local one arm never initialized is
uninitialized (`mdtests/a_bare_branch_joins_arms_that_end_apart.md`,
`mdtests/a_join_leaves_a_local_uninitialized_when_one_arm_does.md`).

The optional interface says more than that: it exports facts and resources both
arms establish. `owns name: resource(...);` in it exports an instance that
carries fields: each arm supplies the instance it has bound to `name`, the join
gives `name` a fresh model, and the interface's `fact` entries are what the
proof knows about it (`mdtests/branch_ensuring_named_resource.md`).

A comparison with `at(mark, ...)` freezes only that marked expression; the
current side is checked in both arms and the joined state.

An interface fact holds in an arm exactly when a `have` of the same text
would there, quantified facts over memory included: both arms proving
`forall k < 2u64 { tmp[k] != 0u8 }` export it
(`mdtests/a_branch_interface_exports_a_quantified_fact_over_a_local_array.md`).

An arm may split its path with a proof `if`. One that ends the arm rejoins its
cases where they end, keeping what both establish, and the join checks the
interface on that rejoined arm; neither case runs to the function exit. One
earlier in the arm rejoins before the rest of it, as at the top level
(`mdtests/a_proof_if_inside_a_branch_arm_rejoins_at_the_join.md`). A fact only
one case proves does not survive that rejoin, so it cannot be exported
(`mdtests/a_proof_if_inside_a_branch_arm_keeps_only_what_both_cases_establish.md`).

**Failure, checking, and tools:**

A non-`if` frontier, overshot arm, unproved interface item, or nondeterministic
join fails. Click follows the spelled arms and interface; expansion recurses
into smart descendants, and profiling classifies those descendants. Exported
facts retain outer proof-binding names for later `at(...)` rewrites, and reads
through local pointers keep their declared element types.

**Checked examples:** [`frontier_branch.md`](https://github.com/clicklang/click/blob/master/mdtests/frontier_branch.md), [`branch_interface_mixes_current_read_and_mark.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_mixes_current_read_and_mark.md), [`branch_interface_keeps_model_pointer_names.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_keeps_model_pointer_names.md), [`branch_interface_loaded_wide_pointer.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_loaded_wide_pointer.md)

### Loop transitions

**Form:** `loop [as name] { ... }`

**Core.** At a C loop frontier, prove initialization and one arbitrary
iteration, construct the loop rule, and advance to its abstract exit. One
iteration is a path that reaches the body's end, a `continue`, a `break`, or a
function `return`: a `continue` is the back edge; a `break` closes no invariant
and joins the loop's ordinary exits; and a `return` is terminal for the function
and owes neither the invariant nor ranking bundle.

A `preserve by { ... }` script works like a function proof. When it ends, or
when its tactics stop inside the body and the rest of the body runs implicitly
to the back edge (splitting at C `if`s like a function's implicit tail,
[`preserve_runs_the_rest_of_the_body.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_runs_the_rest_of_the_body.md)),
the back edge owes the loop's bundle: each declared `invariant`, guarded by
the invariants declared before it, and for a `decreases` loop one `0 <= m`
member per component and one descent member `m < at(<iteration entry>, m)`
(for a tuple measure, the right-nested disjunction over pivots with the
earlier components tied). Each member is closed by `solve()`, exactly as a
function's exit closes each `ensures`; this closes, for example, an unsigned or
64-bit bound and its descent from the guard
([`back_edge_closes_an_unsigned_bound_from_the_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/back_edge_closes_an_unsigned_bound_from_the_guard.md)).
To help a member `solve()` misses, prove it, or a fact it needs, with
`have <invariant> by { ... }` before the back edge. `click expand` prints the
closure as one `have <member> by { ... }` per member at the end of the
`preserve` script, omitting members already available as facts. The retired
`close_invariants` tactic is rejected by the parser
([`close_invariants_is_retired.md`](https://github.com/clicklang/click/blob/master/mdtests/close_invariants_is_retired.md)).

Inside the loop's clauses and phases, `iterations` is the mathematical
`Integer` count of passes completed: `0` when `initialize` checks the
invariants, a fresh `K` with `0 <= K` at the head, and `K + 1` where a pass's
back edge, a `continue` included, checks them again. A `break` leaves during a
pass, which does not count. A `decreases` component may read it too: the
measure is read at `K` where the pass starts and at `K + 1` at its back edge,
so `decreases n - iterations` ranks a loop whose invariants bound the count
([`a_loop_is_ranked_by_its_pass_count.md`](https://github.com/clicklang/click/blob/master/mdtests/a_loop_is_ranked_by_its_pass_count.md),
[`a_measure_that_counts_passes_up_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/a_measure_that_counts_passes_up_is_refused.md)). Past the loop, `loop(i).iterations` names the count
the exit facts state over, on each path that left loop `i`; inside a nested
loop, `iterations` is that loop's own count, and the enclosing proof reads it
as `loop(i).iterations` once the inner loop exits. `iterations` outside a loop,
and `loop(i).iterations` on a path that has not left loop `i`, are refused. In a
loop's clauses and phases bare `iterations` is always the pass count; a
program variable of that name is [`c(iterations)`](../language/index.md#explicit-c-binding-references),
or `rust(iterations)` in a Rust sidecar
([`a_c_local_named_iterations_is_written_c_iterations.md`](https://github.com/clicklang/click/blob/master/mdtests/a_c_local_named_iterations_is_written_c_iterations.md)).
Like any proof `Integer`, it compares with a C value directly, `i == iterations`
([`a_loop_states_a_running_total_over_its_pass_count.md`](https://github.com/clicklang/click/blob/master/mdtests/a_loop_states_a_running_total_over_its_pass_count.md),
[`a_loop_pass_count_names_the_passes_after_the_loop.md`](https://github.com/clicklang/click/blob/master/mdtests/a_loop_pass_count_names_the_passes_after_the_loop.md),
[`a_break_exit_counts_the_passes_before_it.md`](https://github.com/clicklang/click/blob/master/mdtests/a_break_exit_counts_the_passes_before_it.md),
[`a_continue_is_a_pass_of_the_loop.md`](https://github.com/clicklang/click/blob/master/mdtests/a_continue_is_a_pass_of_the_loop.md),
[`an_inner_loop_counts_its_own_passes.md`](https://github.com/clicklang/click/blob/master/mdtests/an_inner_loop_counts_its_own_passes.md)).

The frontier may be one a `branch` arm or a proof-level `if` arm reached, which
is how a loop guarded by a C `if` is proved; the invariants are then established
from the arm's state, with its path condition available.

The loop does not search the facts it entered with for ones its frame
preserves. A fact about memory stated before the loop and needed after it is
carried by the loop's invariants, or afterwards by
[`transport`](#fact-transport) from the point it was stated at.

**Failure, checking, and tools:**

A non-loop frontier or failed invariant, frame, or decrease obligation fails; so
does a path that stops short of all four endings, and exits that reach different
states, which are named rather than dropped. A continuing arm owes the same
bundle as a top-level loop, including the `decreases` the enclosing termination
judgment requires. A member `solve()` misses fails locally, naming that member,
and a ranked loop's diagnostic names the ranking obligations.

Click checks the structural rule; expansion materializes omitted phase proofs,
and profiling reports smart descendants and simple leaves.

**Checked examples:** [`count_to_n_loop_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/count_to_n_loop_invariant.md), [`the_back_edge_ranks_a_reassigned_parameter.md`](https://github.com/clicklang/click/blob/master/mdtests/the_back_edge_ranks_a_reassigned_parameter.md), [`a_summarized_loop_body_return_is_certified_with_its_value.md`](https://github.com/clicklang/click/blob/master/mdtests/a_summarized_loop_body_return_is_certified_with_its_value.md), [`loop_inside_a_branch_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_inside_a_branch_arm.md), [`loop_inside_a_proof_if_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_inside_a_proof_if_arm.md)

### Calls through named contracts

**Form:** `step(Contract)`

**Specialized.** Write it when a call matches several named contracts and the
proof must choose one. At a C call frontier, select an established named
contract's ownership transition and owned footprint for this call only.

**Accepts** a frontier whose next lowered statement is a C call, when
`Contract(f)` is an available fact for the called pointer or function (from
`requires Contract(callback)`, or from `apply` of a theorem that proves it for
`&f`), with the call's signature, and `Contract` declares no named resource
binders:

- The call runs under `Contract`'s ownership transition and owned footprint,
  for this one call only.
- `Contract`'s preconditions are checked as `step()` checks them, and open ones
  go to the implicit closer.
- The successor has `Contract`'s `ensures` and only `Contract`'s resource
  transition. It also has the guarantees of every other applicable contract
  that do not depend on resources, about the same result and post-call memory.

**Outside it**, with what to write instead:

- A frontier that is not a call fails with `requires a call at the current
  frontier`. Step to the call first.
- A contract that is not established for this pointer fails with `is not
  established for this callback`, even when another pointer has it. Establish
  it with `requires` or `apply`.
- An unknown name fails with `unknown call contract`.
- A contract that declares resource binders: use `step(Contract, { ... })`.
- A second call, including one in the same C statement, gets no selection.
  Write another `step(Contract)` for it.
- `step(Contract(...))` is retired, and `step(A, B)` is a parse error.
- When one contract applies, or the applicable contracts carry no resources,
  a plain `step()` is enough. Two applicable contracts that carry resources
  make a plain `step()` fail with `ambiguous callback resource transition`.

**Failure, checking, and tools:**

There is no fallback to another contract. Expansion preserves the selection.

**Checked examples:** [`c_step_contract_buffered.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_buffered.md), [`c_step_contract_selected_footprint.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_selected_footprint.md), [`c_step_contract_shared_result.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_shared_result.md), [`c_step_contract_not_known.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_not_known.md), [`c_step_contract_not_a_call.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_not_a_call.md), [`c_step_contract_same_statement_calls.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_same_statement_calls.md), [`c_step_contract_missing_precondition.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_missing_precondition.md)

### Calls with binder maps

**Form:** `step(callee, { binder: instance, n: value, ... })`;
`let { result: name, binder: name, ... } = step(callee, { ... })`

**Specialized.** Write it at a call whose callee declares instance binders,
to say which owned instance each binder takes; or `let` value parameters, to
give a value the caller cannot supply by holding an instance, such as the
length of the string a local array holds; or `produces` binders, to name the
instances the call creates. The step names the callee's contract, not the
call: the arguments are the call at the frontier's, so it works for calls
whose arguments a proof expression cannot write, such as `cond ? "" : " "`.
The name gives the map its binders, and the produced instances their
resources, before the step runs. `result: name` in the `let` pattern names
the C value.

**Accepts** a frontier whose next lowered statement calls `callee`, when:

- Each instance entry, `{ first: c }`, names an instance the caller holds, of
  the binder's resource; the map has one for each instance binder of the
  callee's contract that is not `produces`
  ([`c_call_binder_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport.md)).
- A resource type binder, such as `atomic_init`'s `payload`, takes a resource
  term, `{ payload: ready_payload(channel) }`.
- Each value entry names a value parameter of the callee's contract,
  `{ n: 0u64 }`, evaluated at the call's state
  ([`step_value_map_gives_a_let_parameter_its_value.md`](https://github.com/clicklang/click/blob/master/mdtests/step_value_map_gives_a_let_parameter_its_value.md)).
  A parameter the map leaves out takes its value from the one held instance
  that agrees with its clause, and the call still requires each clause at
  the chosen values. A string over a local array is assembled from its bytes
  as one over owned bytes is
  ([`a_local_char_array_lends_its_c_string_view.md`](https://github.com/clicklang/click/blob/master/mdtests/a_local_char_array_lends_its_c_string_view.md)).
  `snprintf` is named without its format; the length of the `%s` that
  converts argument `N`, counting from zero, is `nN`, checked against the
  call's format when the step runs
  ([`step_value_map_takes_the_frontier_call.md`](https://github.com/clicklang/click/blob/master/mdtests/step_value_map_takes_the_frontier_call.md)).
- The `let` pattern names every `produces` binder. A produced instance's
  resource arguments are the call's arguments
  ([`c_call_binder_transport_multiple_produces.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport_multiple_produces.md)).
- A callee without binders takes the empty map `{ }`. Use this to name the
  result of `y = g(x);` or `return g(x);`
  ([`call_result_in_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/call_result_in_condition.md)).
  `name` must not be a C variable. A proof name may be rebound.

The step then checks the call as `step()` does, and open preconditions go to
the implicit closer. Mapped instances take the callee's transition, unmapped
caller instances frame, and the callee's `ensures` hold of the mapped and
produced instances.

**Outside it**, with what to write instead:

- A frontier that does not call `callee` fails with `requires a call to
  callee at the current frontier`.
- A missing entry (`call map omits ... binder`), a duplicate one, an unknown
  binder or instance, an instance of another resource, or one instance for
  two binders fails where it is written.
- A name the callee does not declare as a value parameter fails with
  `declares no value parameter`, naming the call
  ([`step_value_map_names_a_parameter_the_callee_lacks.md`](https://github.com/clicklang/click/blob/master/mdtests/step_value_map_names_a_parameter_the_callee_lacks.md)).
- A `produces` binder written in the map is refused. Introduce it in the
  `let` pattern.
- `result: name` on a call whose value is discarded fails with `this call's
  result is unused`. Use `step(callee, { ... })` without it.
- An uncontracted `static inline` helper takes no map. Its body runs at the
  call site; use `step()`.
- The retired spellings `step({ ... })` and `step(callee(args), { ... })`
  are refused with this form
  ([`a_call_step_names_its_callee_not_its_call.md`](https://github.com/clicklang/click/blob/master/mdtests/a_call_step_names_its_callee_not_its_call.md)).

**Failure, checking, and tools:**

The input map and output pattern are the only sources of bindings; nothing is
searched or inferred. Expansion reprints both unchanged.

A call publishes the callee's postconditions. It does not search memory history
to turn symbolic reads in those postconditions into extra constant equalities.
Establish the needed read equality in the proof; use `preserve(...)`
when it crosses a memory effect. Already-available equalities remain usable by
`known()` and explicit arithmetic or rewrite steps.

**Checked examples:** [`c_call_binder_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport.md), [`c_call_binder_transport_multiple_produces.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport_multiple_produces.md), [`call_result_in_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/call_result_in_condition.md), [`call_step_binder_map_on_an_uncontracted_inline_helper_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/call_step_binder_map_on_an_uncontracted_inline_helper_rejected.md)

### Named contracts with resource bindings

**Form:** `step(Contract, { handle: instance, ... })`; `step(Contract, { binder: instance })`

**Specialized.** Write it to choose a named contract and map its resource
binders in one call step. Select an established named contract for the current C
call and map its resource binders. The same `let { result: value, output:
resource }` pattern binds its C value and produced resources.

The two spellings in **Form** are the same form. A handle is a named resource
clause (`owns model: Ledger();`, `consumes input: Dirty(p);`) of the
contract.

**Accepts** a call frontier with `Contract(f)` established for the called
pointer or function, with the call's signature, as for `step(Contract)`, when:

- The map has one entry for each binder of `Contract` that is not
  `produces`. Each entry names a distinct instance the caller holds, of that
  binder's resource.
- The `let` pattern names every `produces` binder, plus `result: value` when
  the call's value is used.

The C arguments come from the call. Preconditions are checked as for
`step(Contract)`, with open ones going to the implicit closer. The successor
has `Contract`'s `ensures` over the mapped and produced instances, and the
resource-free guarantees of other applicable contracts.

**Outside it**, with what to write instead:

- A missing input binder fails with `call map omits ... binder`. An unknown
  binder fails with `declares no resource instance binder`. An instance of
  another resource fails with `binder ... expects resource`.
- A `produces` binder in the map, or one missing from the pattern, fails with
  `produces ...; introduce it with let`. Write
  `let { output: name } = step(Contract, { input: instance })`.
- A contract that is not established for this pointer fails with `is not
  established for this callback with its call signature`. Establish it as for
  `step(Contract)`.
- A contract with binders written without a map, `step(Contract)`, is refused.
- A contract without binders: write `step(Contract)`.

**Failure, checking, and tools:**

Preconditions and ownership transitions use the existing call checker.
Expansion reprints the map and pattern unchanged.

**Checked examples:** [`named_contract_call_output_bindings.md`](https://github.com/clicklang/click/blob/master/mdtests/named_contract_call_output_bindings.md), [`c_step_contract_resource_count_is_model_local.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_resource_count_is_model_local.md)

### One statement obligation

**Form:** `step(...) by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
an obligation a different proof than the implicit closer. Any `step` form,
including `let` and call forms, followed by the proof of the one obligation its
primitive generates. Emitted verification conditions and call preconditions
remain obligations even when known: their ordinary `solve()` proof is usually
`known()`. Arithmetic evaluation still has safety decisions that precede
obligation generation; those are not yet migrated.

The body proves that obligation at the step's pre-state, as a `have` would, and
the step then runs with it stated. The body is one tactic call, such as
`solve();`, or a block.

**Failure, checking, and tools:**

Refused when the operation generates no obligation (superfluous) or more than
one; the second refusal spells every open obligation as a `requires` entry to
copy. The default `step()` already invokes the implicit closer for open obligations, so
write `step()` rather than a `by` that only repeats it. Expansion keeps the
`by` and prints the body's checked steps. The form is checked in a claim's
linear script and in a `branch` arm
([`step_by_and_requires_in_a_branch_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/step_by_and_requires_in_a_branch_arm.md)).

**Checked examples:** [`step_by_proves_its_one_open_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/step_by_proves_its_one_open_obligation.md)

### Several statement obligations

**Form:** `step(...) { requires P by ...; }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
several open obligations their own proofs. Any `step` form followed by one
`requires [label:] P by ...;` entry per obligation it proves. Each `P` is
written at the step's pre-state over the caller's locals and the call's
arguments, must state exactly one generated obligation, and is
proved there as a `have`.

Entries may appear in any order. An obligation no entry writes is checked as a
bare `step()` checks it.

**Failure, checking, and tools:**

An entry that states no generated obligation, or that repeats an earlier entry's obligation, fails where it is written
and lists the open obligations. Expansion keeps each entry and prints its body's
checked steps. Like the `by` form, it is checked in a `branch` arm.

**Checked examples:** [`step_requires_proves_each_open_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/step_requires_proves_each_open_obligation.md)

## Proposition reasoning

Checked equality closure also records a contradiction when one typed scalar
class contains unequal 32-bit or 64-bit constants, including classes connected
through model getters, or when one model class contains two different
constructors. Two applications of one constructor in a class have equal fields,
so `x == Full(a)` and `x == Full(b)` give `a == b` to `solve` and `known()`
without a stated `Full(a) == Full(b)`; see
[`constructor_injectivity_through_an_equal_value.md`](https://github.com/clicklang/click/blob/master/mdtests/constructor_injectivity_through_an_equal_value.md). Semantic fact lookup and inconsistency checking use this
indexed evidence, so `known()` can close a goal in that impossible context
without another search. The evidence belongs to the current branch and is
rebuilt when a context is restricted to selected facts; it does not equate reads across
version points where memory may have changed. Exact fact membership remains separate. See
[`model_getter_constant_conflict.md`](https://github.com/clicklang/click/blob/master/mdtests/model_getter_constant_conflict.md).

`extract(P)` can also project an available disjunction: each source arm
must establish `P` through its direct `and`/`or` structure and equality-backed
fact lookup. It selects stated disjunctions indexed by the values or addresses
`P` names, without scanning unrelated facts, unfolding functions, or searching
for theorems. It checks every arm and keeps their assumptions local. For example,
`(A and X) or (B and Y)` supplies `A or B` without spelling `X` and `Y`.
See [`extract_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_disjunction_projection.md)
and [`loop_exit_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_exit_disjunction_projection.md).

A simple tactic that adds a fact (`extract`, `instantiate ... using`,
`apply ... using`, `transport ... using`, and `obtain`) also closes a
proposition goal that it adds, when it is the last written step or only
`known`, `solve`, or `normalize` follows it. An added order fact closes
the goal under either spelling of the same claim: `0 <= e` closes the goal
`e >= 0`, and `a < b` closes `b > a`, for machine and `Integer` operands
alike. A written theorem application also closes the mirrored goal when
its checked conclusion was already stated in the context. When other written
steps follow, the goal stays open with the added fact available, so every remaining
step is still checked.

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `both { ... } and { ... }` | control | Expansion output | Prove both sides of a conjunction. | [Reference](#conjunctions) |
| `outcomes { returned => { ... } threw => { ... } }` | control | Specialized | Prove each returned or exceptional outcome. | [Reference](#execution-outcomes) |
| `solve()` | smart | Core | Close one goal from available facts and bounded rules. | [Reference](#simplification) |
| `solve() using { P; ... }` | smart | Specialized | Close one goal from written premises only. | [Reference](#simplification-with-selected-premises) |
| `known()` | simple | Expansion output | Close a goal from available facts or goal-local computation. | [Reference](#available-facts) |
| `extract(P)` | simple | Expansion output | Extract a proposition from an available fact. | [Reference](#extracting-a-fact) |
| `normalize()` | simple | Expansion output | Close a goal by evaluation without context. | [Reference](#context-free-normalization) |
| `normalize() using { P; ... }` | simple | Expansion output | Check normalization against written premises. | [Reference](#normalization-with-selected-premises) |
| `preserve(separate(region.footprint, resource))` | simple | Specialized | Preserve a selected read across a separated effect. | [Reference](#preservation) |
| `arithmetic_certificate { premise ...; conclusion N; }` / `arithmetic_certificate signed_int32 { ... }` / `arithmetic_certificate rules { ... }` | simple | Expansion output | Check explicit arithmetic evidence. | [Reference](#arithmetic-certificates) |
| `rewrite(from, to)` | simple | Core | Rewrite the goal using an equality. | [Reference](#rewriting) |
| `intro()` | simple | Core | Introduce a universal binder or implication premise. | [Reference](#introducing-a-binder-or-premise) |
| `intro() as name` | simple | Specialized | Choose the name introduced into the proof. | [Reference](#naming-an-introduced-binder) |
| `enumerate()` | simple | Expansion output | Close a constant-bounded universal from its instances. | [Reference](#finite-enumeration) |
| `contradiction(P)` | simple | Core | Close a goal from incompatible facts. | [Reference](#contradictions) |
| `instantiate(F, value)` | simple | Specialized | Instantiate an available universal fact. | [Reference](#universal-instantiation) |
| `instantiate(F, value) using { P; ... }` | simple | Expansion output | Instantiate using written premises. | [Reference](#instantiation-with-selected-premises) |
| `apply(theorem(args))` | smart | Core | Apply a theorem, looking up its premises. | [Reference](#theorem-application) |
| `apply(theorem(args)) using { P; ... }` | simple | Expansion output | Apply a theorem using written premises. | [Reference](#theorem-application-with-selected-premises) |
| `unfold(function(args))` | simple | Core | Open one layer of a pure function. | [Reference](#unfolding-pure-functions) |
| `peel(function(args)) using { P; ... }` | simple | Specialized | Open a function using written branch evidence. | [Reference](#peeling-a-pure-function) |
| `match value [ensuring { ... }] { Type::Variant(fields) => { ... } ... }` | control | Core | Prove each constructor case of an algebraic value. | [Reference](#constructor-matches) |
| `induct(n) as ih` | simple | Core | Introduce strong induction on a nonnegative `int32` or a `uint64`. | [Reference](#scalar-induction) |
| `induct(xs) as ih { Type::Variant(fields) => { ... } ... }` | control | Core | Prove constructor cases with recursive hypotheses. | [Reference](#algebraic-induction) |
| `apply(ih(m))` | smart | Core | Apply an induction hypothesis, looking up its premises. | [Reference](#induction-hypothesis-application) |
| `apply(ih(m)) using { P; ... }` | simple | Expansion output | Apply an induction hypothesis using written premises. | [Reference](#induction-hypotheses-with-selected-premises) |
| `have P by { ... }` | control | Core | Prove and retain a named or unnamed fact. | [Reference](#intermediate-facts) |
| `if P [ensuring { ... } then] { ... } else { ... }` | control | Core | Split a proof on a chosen proposition. | [Reference](#proposition-branches) |
| `cases { A => { ... } B => { ... } }` | control | Specialized | Prove a written collection of cases. | [Reference](#explicit-cases) |
| `open(resource) { ... }` | control | Specialized | Unfold a resource for a nested proof. | [Reference](#scoped-resource-opening) |
| `open(...) { ... } by { ... }` | control | Expansion output | Supply the proof that restores an opened resource. | [Reference](#scoped-resource-opening-with-restoration) |
| `witness { name: value, ... };` | simple | Specialized | Supply values for existential binders. | [Reference](#existential-witnesses) |
| `obtain (name: Type, ...) { P }` | simple | Specialized | Name witnesses from an available existential fact. | [Reference](#obtaining-witnesses) |

`sorry()` is a dev-only proof hole, not a tactic for committed proofs: it
parses only under `click verify --allow-sorry` and closes its goal without
checking it. See [Dev-only proof hole](../cli/verify.md#dev-only-proof-hole).

When `intro` must freshen a universal binder, it uses the reserved logical-witness
range. Existential choices use that same range, separate from C execution,
load and binder identities. Issued witnesses remain reserved even when their
instantiated body does not mention them, so later introductions and choices
cannot reuse a live proof binding. Narrow machine binders also supply their
intrinsic bounds at introduction; these type facts need no extra `intro()`.
A written range quantifier still has its explicit range-membership guard.

`both { ... } and { ... }` proves an `A and B` goal by opening the exact `A`
and `B` child goals. Both arms inherit the parent assumptions; neither inherits
facts proved only in the other arm. This differs from `known()`, which
closes a conjunction from already-established facts. Empty or unfinished arms fail.
The `both` source location owns expansion and profiling of its nested proof;
expansion preserves both bodies with their checked steps.

`by solve();` is sugar for a script containing the same `solve()` operation at
the same proof state, followed like every script by the implicit tail. A
`solve()` written before execution has reached the function exit is refused
with the frontier it stands at; the end of a body is one `step()` of its own
(`mdtests/solve_before_exit_in_arm_names_the_frontier.md`).

Inside a `have` body, a tactic that already closed the goal (an `unfold`
whose refreshed goal is an available fact, a `transport` onto the goal, a
theorem whose conclusion is the goal) may be followed only by `known`,
`solve`, or `normalize`, which then assert the closed judgment and emit
nothing. So `unfold(f(x)); normalize();` means the same whether or not the
unfold alone closed the goal
(`mdtests/closer_after_unfold_closed_goal.md`); any other tactic after the
closure is refused by naming the tactic that closed it
(`mdtests/tactic_after_closed_goal_is_named.md`).

`induct` is available only in a pure theorem, must be the first tactic, and
names a proof-local hypothesis. The algebraic form is the enclosing control
tactic and therefore the only top-level tactic; its constructor arms contain
the proof steps. It is never inserted by `solve` or the implicit closer.

The algebraic hypothesis takes the theorem's complete parameter list in
declaration order. Only the inducted position is restricted: it must name a
field the current arm's pattern bound, of the datatype being inducted on.
Every other position may name any well-typed term, which is how a proof whose
recursive case changes another parameter — an accumulator, or a context frame
that grows the focused subtree — states its hypothesis. Passing only the
inducted argument remains the spelling for "every other parameter unchanged",
so `ih(tail)` and a complete list that repeats the other parameters are the
same instance. Each instance carries the theorem's `requires` clauses
substituted at the arguments given; a `using` block, or the premises the bare
form plans, must prove exactly those.
A theorem application's arguments and its `using` premises are written in
the same scope as a `have` goal at that point of the proof: the goal's own
binders first, then every proof local, including the bindings a proof
`match` arm introduced, the names a `let { ... } = unfold(...)` gave its
children, a `let { result: r } = step(...)` result, and a loop binder. The C null pointer constant
is accepted at a pointer-typed theorem parameter and lowers to that
type's null value, as it does at a pure function's pointer parameter.
`instantiate` and `extract` resolve their written propositions the same way.
See [`theorem_argument_arm_binding.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_arm_binding.md),
[`theorem_argument_arm_binding_algebraic.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_arm_binding_algebraic.md),
and [`theorem_argument_null_constant.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_null_constant.md).

Bare `apply(ih(m))` is smart because it plans proofs of the fixed application
obligations. Its expansion ends in the deterministic simple
`apply(ih(m)) using { ... }` operation, which checks exactly the listed
nonnegative, strict-decrease, and substituted-requirement facts.

`enumerate` is how an explicit proof closes a finite case analysis over a
constant-bounded universal, such as a `sorted(p, 3)` postcondition: the
expanded proof spells one `have` per non-vacuous instance (typically closed by
`intro`, `instantiate ... using`, an explicit transport, and `known`),
and `enumerate()` checks exactly those instances against the goal's own
guard-derived ranges. A goal stated as a predicate call is unfolded to the
body that binds the instances, and the smart `solve` proves nearest pairs
first so a wider span can cite its neighbours. Instances are lowered lazily: a missing instance stops `enumerate` before
visiting the rest of the numeric range, and smart `solve` also stops generating
instances at its first failed proof. The finite-universal planner and its
retained certificate checker use the same lazy range order and still require
every in-range instance for success. This keeps refusal of a false frame over
a large constant range from materializing every element. Click never
instantiates by search: an in-range instance that is neither vacuous nor
spelled fails.

Proof-level `if` and `cases` answer different questions. `if P` is an
excluded-middle split: the else case assumes `not P`, so it cannot eliminate a
disjunctive fact whose right side is not the negation of its left. `cases`
requires proof that its written alternatives are exhaustive, then checks each
branch under exactly its assumed disjunct. The ordinary implicit closer can
establish the disjunction from available facts, and expansion retains that
proof as a preceding `have`. An explicit `have` can establish it without
implicit search. This permits equivalent or reordered alternatives; a branch
that needs another arm's disjunct still fails. Complementary alternatives
retain the kernel's direct split evidence.

Intrinsic tactic class and selectable source-site kind answer different
questions. `have` is always a control container because it owns a nested goal.
Its selectable source site is an expandable-automation site for a supported
smart body, a simple-operation site for a nonempty entirely simple body, and a
control-container site otherwise. A `loop` is likewise intrinsically control;
when a phase proof is omitted, the `loop` keyword is the source site
that owns the generated automation. Profiling renders those site kinds as
SMART, SIMPLE, and CONTROL, while smart-site discovery and expansion select
only expandable-automation sites.

Explicit full-width unsigned bounds can also normalize pointer offsets.
For a native uint64 `index <= 2147483647u64`, `pointer + index` and
`pointer + index as int32` denote the same address. `solve() using { ... }` checks
that the cited native bound is available and preserves the pointer stride.
A bound on the low word or a signed comparison cannot establish this unsigned
projection, and address equality grants no permission to access the backing
storage. Conditional normalization does not enter binder bodies.

When a smart `have` needs memory permissions merely to lower its goal, its
expanded proof retains the relevant viewability and order facts through
explicit transports, rewrites, extracts, or named theorem applications. A
context-free-looking result such as a normalized equality is not emitted as
bare `normalize()` if checking still needs those premises to interpret an
indexed load. A `solve() using` equality may be selected through a bounded chain
of exact equality facts whose intermediate load variables are kernel-internal
names for the same user-level loads. When frame evidence is needed to relate an
earlier load origin to the current one, the expanded proof first establishes the
current surface form with an explicit `transport`; simple `rewrite` checking
never searches for an equivalent equality. Expansion and audit verify the
complete rewritten surface proof through the ordinary entry point.

### Conjunctions

**Form:** `both { ... } and { ... }`

**Expansion output.** `click expand` writes it; by hand, a conjunction goal is
normally split by `solve` or the implicit closer; write `both` only when each side needs its
own explicit proof. Prove the exact left and right children of an `and` goal in
separate scopes.

**Failure, checking, and tools:**

A non-conjunction or unfinished arm fails. Arms inherit only the parent
assumptions. The source container owns expansion of its nested proof.

**Checked examples:** [`proof_both_and.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_both_and.md)

### Execution outcomes

**Form:** `outcomes { returned => { ... } threw => { ... } }`

**Specialized.** Write it at a C++ call that may throw, when the two outcomes
need different proofs; the implicit tail splits them for you. At a maybe-throwing
call, prove its two successors separately; each arm begins with the `step()`
that runs the call along its edge. Inside a `try`/`catch (int name)` the `threw`
arm follows the caught exceptional edge into the handler.

Outside any `try` the `threw` arm ends at function exit with that throw, while
the `returned` arm continues with the rest of the function and may hold the next
call's own nested `outcomes`. The implicit tail splits every maybe-throwing call this
way, inside a C `if` arm as well as at top level, and expansion writes the split
it took.

**Failure, checking, and tools:**

The checked execution must establish exactly one edge of each kind. Each arm has
its own outcome goal and must close it; neither arm can use the other's facts or
state. Expansion preserves both certificates.

**Checked examples:** [`cpp_import.rs`](https://github.com/clicklang/click/blob/master/tests/cpp_import.rs), [`outcomes_routes_a_throw_that_leaves_the_function.md`](https://github.com/clicklang/click/blob/master/mdtests/outcomes_routes_a_throw_that_leaves_the_function.md)

### Simplification

**Form:** `solve()`

`solve()` closes one goal and runs no C. The parser refuses a written `auto();`, naming
`solve();` for it and the omitted proof for `by auto();`. `by solve();` restates what an omitted proof of a
`have` or a pure theorem's `ensures` does, but it is accepted: it marks a place
to write a different tactic later.

**Core. On a proposition goal, search ambient pure facts and bounded rules for
a simple proof. A signed `int32` goal over variables is tried with one
arithmetic certificate from the indexed bounds reachable from those variables (a
bound `i < n` leads on to `n`'s bounds, up to eight variables), the same way in
a pure theorem, before execution, mid-function, in a `branch` arm, and at
function exit; a negated branch condition counts as a bound. Constant bounds on
the goal variables are tried before following relational bounds, so earlier
postconditions on those variables do not exhaust the arithmetic premise limit.

An equality of two `uint32`, `int64` or `uint64` values closes from the two
opposite order facts on its operands, `a <= b` and `b <= a` in any spelling
(`a >= b`, `not (a < b)`), looked up exactly and cited by one `solve()
using` step
([`solve_closes_an_equality_from_opposite_bounds_at_every_width.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_closes_an_equality_from_opposite_bounds_at_every_width.md)).
An unsigned `x == 0` needs only `x <= 0`, since no unsigned value is below zero.

A loop bundle closer's members cite only the loop head and the contract instead.
Its arithmetic first tries the named premises whose variables occur in that
member's goal, then the complete named slice when other variables are needed.
A conjunction under implications or universals is first tried leaf by leaf with
direct logical steps, and a written conjunction is split before any search over
the whole goal, each conjunct trying direct steps first.

An implication whose antecedent `normalize()` refutes, such as
`i == i + 1 implies n <= 5u64` with Integer `i + 1`, is introduced and closed
by `contradiction` on that antecedent, reading only the goal; expansion
writes `intro(); contradiction(A);`
([`an_antecedent_normalization_refutes_closes_its_implication.md`](https://github.com/clicklang/click/blob/master/mdtests/an_antecedent_normalization_refutes_closes_its_implication.md)).
An implication whose antecedent, or one conjunct of an `a and b` antecedent,
has its opposite among the facts closes by `contradiction` once `solve`
introduces it, whichever spelling the facts state the opposite in (`x > 100`
for `x <= 100` false), so `a and b implies c` closes where the curried
`a implies b implies c` does
([`solve_refutes_a_conjunct_of_an_antecedent.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_refutes_a_conjunct_of_an_antecedent.md),
[`solve_keeps_a_conjunct_antecedent_that_holds.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_keeps_a_conjunct_antecedent_that_holds.md)).

A goal that is one conjunct of an implication's consequent, `c == 2` from
`a != 0` and `a != 0 implies (b == 1 and c == 2)`, is closed once the
antecedent is an available fact: the closer extracts the whole consequent,
spelled as the implication is written, and the goal is then a proper
conjunct; expansion writes the `extract`
([`solve_closes_a_conjunct_of_a_discharged_consequent.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_closes_a_conjunct_of_a_discharged_consequent.md)).

A comparison held only under a definedness guard (`defined(e) implies a == b`,
as a call postcondition over partial arithmetic lowers) whose consequent names a
goal operand is used once a nested `solve` proves the guard: the closer extracts
the consequent and rewrites the goal with an equality or closes from the new
fact.

An `int32` or `int64` definedness goal `defined(a + b)` or `defined(a - b)` is
closed by the checked `int32_defined` or `int64_defined` certificate rule,
citing the constant order and equality facts of that width indexed under each
operand; the rule, not the selection, decides whether the operands' ranges
exclude overflow.

A recursive specification function applied to a known constructor is
evaluated: `solve` unfolds it, then keeps unfolding the recursive calls the
definition exposes while their arguments select one arm, rewriting an argument
by a constructor equation (a supplied premise or a connected fact such as
`u == Tree::Node(..)`) when that exposes one, for at most eight checked steps.
An argument nothing fixes stays folded
([`solve_evaluates_a_recursive_function_over_known_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_evaluates_a_recursive_function_over_known_constructors.md),
[`solve_does_not_evaluate_a_recursive_function_past_an_unknown_argument.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_evaluate_a_recursive_function_past_an_unknown_argument.md)).

An existential `exists v { x == C(.., v, ..) }` whose `x` a fact fixes to a
constructor of the same variant, `x == C(.., t, ..)`, takes `t` as its witness:
`solve` writes `witness { v: t }` and closes the instance. A constant payload is
written as itself and any other value by the local, parameter or binder that
holds it; a value of another variant gives no witness
([`solve_takes_a_known_constructor_payload_as_the_witness.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_takes_a_known_constructor_payload_as_the_witness.md),
[`solve_finds_no_witness_in_another_variant.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_finds_no_witness_in_another_variant.md)).

A disequality between an algebraic value and a constructor closes from an exact
equality fixing that value to a different constructor: the equality rewrites the
goal and normalization decides the constructors differ
([`solve_constructor_disequality_from_produced_field.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_constructor_disequality_from_produced_field.md)).

An `int32` or `int64` definedness goal whose operand is a sum with a summand an
exact equality fixes to `0`, such as a count `A + n` with `A == 0`, first proves
the operand equal to the sum without it by `solve`, then the restated goal from
its bounds
([`solve_defined_count_after_a_zero_summand.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_defined_count_after_a_zero_summand.md)).

When the goal also carries an operand's own definedness, such as a field read
through a resource, `solve` proves `defined(operand)` as a `have` and cites it in
the `int32_defined` step
([`solve_defined_read_through_a_produced_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_defined_read_through_a_produced_resource.md)).

A goal that reads one cell at two version points, such as `owner->cell[0] ==
owner->phase` right after a store wrote the first side from the second, is
proved by `transport` from the cell's reflexive equality at a recently recorded
point, with the frame evidence the transport selects as its `using` list
([`solve_frames_a_read_across_a_separate_store.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_frames_a_read_across_a_separate_store.md)).

A goal that reads memory and held at the function's entry or at one of the 8
most recently recorded points is proved by one `transport` from that point,
with the frame evidence the transport selects. A read written through one
alias of a cell whose fact was stated through another, across a store the
context's facts keep separate from it, is carried this way: lowering keeps the
read as written
([`fold_argument_reads_through_model_pointer.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_argument_reads_through_model_pointer.md)).
A fact from an older point needs an explicit `transport`.

A goal that is one disjunct of an available disjunction whose every other
disjunct an exact fact refutes is proved by `cases` over that disjunction, the
refuted arms closing by `contradiction`
([`solve_disjunctive_syllogism.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_disjunctive_syllogism.md)).

A goal that an available implication (or chain) concludes whose antecedents are
exactly available, such as a call guarantee `r == 0 implies X` inside the branch
where `r == 0`, is closed by modus ponens as a direct step through `extract`'s
indexed consequent lookup, with the goal's `at(...)` points as written; an antecedent
that is not exactly available is not proved or searched for.

A guarded universal goal `forall k { G implies A }` closes from an available
`forall k { G implies A and B }` with the same binder and guards, selected by one
indexed lookup of the conjuncts guarded universals conclude. The proof is `intro()`
for the binder and each guard, `instantiate` at the introduced binder, and
`known()`, so `memset`'s `defined(..) and` value postcondition supplies
`bytes::all_equal`
([`solve_drops_a_conjunct_of_a_guarded_memset_postcondition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_drops_a_conjunct_of_a_guarded_memset_postcondition.md)).
A different guard or an unstated conjunct is not supplied
([`solve_does_not_weaken_a_guarded_universal_to_a_wider_range.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_weaken_a_guarded_universal_to_a_wider_range.md),
[`solve_does_not_drop_a_conjunct_a_universal_lacks.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_drop_a_conjunct_a_universal_lacks.md)).

Case splits consider only disjunctions sharing a variable with the goal, nested
at most twice. Equality rewriting chains through the goal's equalities,
including a scope's own `have`s and pointer equalities reaching the goal's loads
through their addresses; each link keeps up to four goal-changing rewrites,
continuing from the first and probing the others one link further.

It never executes C.

**Failure, checking, and tools:**

A bounded miss leaves the goal open and reports the target. Click checks the
chosen operations; expansion prints its proof steps, and profiling reports
search plus leaves.

**Checked examples:** [`solve_postconditions.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_postconditions.md)

### Simplification with selected premises

**Form:** `solve() using { P; ... }`

**Specialized.** Write it when `solve` picks the wrong premises or searches too
long, to restrict it to the named facts. On a proposition goal, including a
contract claim after function exit, search using exactly the listed proposition
facts. A preceding `have` is available on each outcome where it was proved;
grouped proposition and ownership claims retain their checked resource
transition.

A listed guarded equality whose definedness guard is not listed has the guard
proved first, from the other listed facts when they suffice, and is then used as
its consequent. An `int32` or `int64` definedness goal cites the listed premises
that bound an operand by a constant in one `int32_defined` or `int64_defined`
certificate. For an Integer goal observing a machine sum or difference,
listed bounds and the machine type's range can establish the in-range
identity, such as `to_integer(x + 1) == to_integer(x) + 1`. Expansion writes
the range proofs and an `integer_operation_identity` certificate. An
unsigned operation is used this way only when those bounds prove it does not wrap.

**Failure, checking, and tools:**

A missing fact or missing simple rule fails. Click uses the generated explicit
proof rather than repeating search; expansion emits the named steps or reports
the rule gap, and profiling reports the restricted site.

**Checked examples:** [`condition_search_explicit_decomposition.md`](https://github.com/clicklang/click/blob/master/mdtests/condition_search_explicit_decomposition.md)

### Available facts

**Form:** `known()`

The former spelling `assumption()` is refused with a diagnostic naming
`known()`. It reuses available facts and also checks the computational leaves
described below.

**Expansion output.** `click expand` writes it; by hand, write it to close a
goal that is already available or true by direct computation, without search,
typically after a `rewrite`. It closes the goal or refuses; it adds no fact.

Smart closure uses `known()` for computational leaves, including residuals
after a rewrite or unfold and leaves inside logical proofs. Pure proofs and
returning paths expand to `known()` or explicit derivations, with no generated
plain `normalize()`. Selected-premise `normalize() using { ... }` and the
divergent-path vacuity closer remain. Explicitly written `normalize()` is
preserved.

**Accepts** a goal that is available, where an atomic proposition is
available when one of these holds:

- It is a fact, or a leaf conjunct of a fact. An implication or quantified
  goal must be such a fact up to renaming of its bound variables.
- It is another spelling of an available order claim, in every order family
  (C machine types and `Integer`): `0 <= x` for `x >= 0`, and `not(y <= x)`,
  `y > x` and `x < y` for one another. `x != y`, `not(x == y)`, and
  `y != x` are one claim.
- The shared equality closure decides it. Equality is symmetric and
  transitive, and congruent through C and `Integer` operators, pure-function
  applications, and algebraic constructors: `x == y` gives `y == x`,
  `x + 1 == y + 1`, `f(x) == f(y)` and `Some(x) == Some(y)`; two equal
  applications of one constructor give their fields' equality. A condition is
  decided on its equality classes: `x < y` and `y == z` give `x < z`, and
  `x != y` and `y == z` give `x != z`. The closure includes checked
  algebraic model aliases.
- It is a native comparison and the `Integer` comparison of its operands'
  exact observations is available, or the reverse: `x < y` and
  `to_integer(x) < to_integer(y)` are interchangeable.
- At a completed C outcome, it is a condition stated at another point
  and the memory history shows each cell it reads unchanged between the two
  points under the facts in context. Only facts that are that same
  condition up to their points are checked, so nothing is searched.

A leaf also closes by goal-local computation: a constant truth, exact
reflexivity (excluding IEEE floating-point comparisons), equality or inequality
of literal integers, cancellation and regrouping of additive machine or
`Integer` expressions, and distinct algebraic constructors. Exact `Integer`
order comparisons close when their symbolic terms cancel. Calls, reads, folds,
and symbolic matches are opaque operands; their identical occurrences may
cancel, but this check never unfolds a call or resolves a read. It does not
invoke the general atomic prover.

Goal-local interval checks also use native type bounds, conditional branch
hulls, casts, and supported arithmetic when the resulting interval decides
the comparison; wrapping operations conservatively lose their tighter bounds.
Negated computational conjunctions and disjunctions are evaluated structurally.
Direct snapshot metadata can establish allocation bounds and initialized
integer reads, including a fixed-width read covered by cached bytes. This
never resolves the read value, follows aliases, or walks store history;
uncertain lifetime or initialization metadata causes a refusal.

A conjunction goal closes when every conjunct does, and a disjunction goal
when one disjunct does, using available facts or these computations recursively.
Computational truths inside an implication or quantifier still require the
ordinary introduction or witness steps. An implication or quantified goal
already held as a fact retains its existing exact-lookup behavior.

**Outside it**, with what to write instead:

- A consequent of an available implication: `extract(Q)` first.
- A reordered disjunction fact (`y > 0 or x < y` from `x < y or y > 0`):
  `extract(y > 0 or x < y)`, which checks each arm, then `known()`.
- A weaker or derived bound, such as `x <= y` from `x < y`: `solve()
  using { x < y; }`.
- An implication or quantifier whose body is only equivalent to a fact, such
  as `y > x implies 0 < y` from `x < y implies y > 0`: `intro()`, then close
  the body.
- A fact from another point whose reads that check does not show
  unchanged: an explicit transport step first.

**Failure, checking, and tools:**

The structural walk checks each needed leaf using indexed facts or direct
computation. A failure names the first side it cannot close; prove other
missing premises with `have` first.

For exactly named, independently held resources, `known()` applies the
live partition rule: an owned unit is separate from another owned unit or a
view. Two views alone do not establish separation. The rule uses exact resource
lookups; it does not enumerate aliases or compositions, and supported cached
projections do not count as independent entries. It also applies to separation
leaves in a conjunction. Constant byte spans with a common symbolic address
can also establish disjointness or containment directly. The partition index
identifies complete constant spans and single symbolic elements by their
physical bytes across differing element units; it grants no access authority.

An explicit `have separate(...)` can use the live ownership partition
immediately after `unfold`, including fixed-size fields fully contained in
different owned objects; it checks complete byte coverage and grants no new
ownership. It also selects two different resources of any kind that the
state owns exactly as written, for example a just-folded resource instance
and a cell owned beside it. `split()`, `left()` and `right()` were folded into this tactic and
are refused with that advice.

Lookup also accepts certified identity of a resource separation. It performs
no function unfolding, implication extraction, or fact transport across
effects. Expansion leaves the step unchanged, and profiling charges one
simple leaf.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`known_computes_fast_leaves.md`](https://github.com/clicklang/click/blob/master/mdtests/known_computes_fast_leaves.md), [`known_closes_an_evaluated_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/known_closes_an_evaluated_goal.md)

### Extracting a fact

**Form:** `extract(P)`

**Expansion output.** `click expand` writes it; by hand, write it to state one
conjunct or consequent of a fact before a step that needs it spelled. It adds
`P` as a fact and closes the goal when the goal is then a fact. Written steps
after a closing `extract` are still checked, and they see all of `P`
([`extract_before_more_steps_keeps_the_whole_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_before_more_steps_keeps_the_whole_fact.md)).

**Accepts** `P` when one of these holds:

- `P` is a proper sub-conjunction of a conjunction fact: a leaf conjunct, or
  a parenthesized group of conjuncts exactly as the fact is built. `and`
  associates to the left, so `a and b` is a sub-conjunction of `a and b and
  c` while `b and c` is not. A leaf may be written in another polarity or
  direction (`0 < y` for the conjunct `y > 0`), and a quantified conjunct
  under renamed binders.
- `P` is the consequent of an available implication fact, exactly as written
  there (up to renaming of quantified binders), and every antecedent before
  it is available in the sense of `known()`'s atomic rules: `A implies B
  implies C` with `A` and `B` available gives `C`, and with `A` alone gives
  `B implies C`.
- `P` is a field equality `a == c` of an exact equality between two
  applications of one algebraic constructor, `K(a, b) == K(c, d)`, at the
  same field position and in that orientation.
- Some available disjunction connected to `P`'s atoms has every arm, assumed
  with the ambient facts, establish `P` by `known()`'s rules, including
  the equality closure: `(x < 5 and y == 1) or (x < 5 and y == 2)` gives
  `x < 5`, and also `y == 1 or y == 2`.

Each leaf conjunct of a fact is already an available fact, so `extract` of a
leaf conjunct adds nothing; every tactic, including `known()` and an
arithmetic certificate's premises, may cite it directly.

Between execution steps and after execution, a bare `extract(P)` adds `P` to
the current state exactly as `have P by { extract(P); }` does.

**Outside it**, with what to write instead:

- `P` that is itself a whole fact, or a regrouped or reordered selection of
  conjuncts (`x < y and z == 1` from `x < y and y > 0 and z == 1`): cite the
  fact directly, or build the conjunction with `have P by { known(); }`.
- A part of an implication's consequent: extract the whole consequent, then
  extract the part
  ([`extract_takes_an_implication_consequent_whole.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_takes_an_implication_consequent_whole.md)).
- A consequent whose antecedent is not available, including a conjunction
  antecedent that is not itself a fact: prove it with `have` first.
- A consequent written in another spelling than the implication's: extract
  it as written, then close with `known()`.
- A consequence an arm establishes only by arithmetic or evaluation (`x != 3`
  or `x < 3` from `x == 1 or x == 2`): `cases { x == 1 => { ... } x == 2 =>
  { ... } }`, rewriting and normalizing in each arm.
- Modus ponens with an implication that is a conjunct of a fact rather than
  a fact itself: `extract` the implication, then its consequent.

**Failure, checking, and tools:**

A refusal names the requested proposition in its written syntax, retaining
parameter and proof-local names. Click follows an indexed, checked
derivation with no search; expansion is unchanged, and profiling charges that
derivation.

**Checked examples:** [`extract_refusal_keeps_written_parameter_names.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_refusal_keeps_written_parameter_names.md), [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`algebraic_symbolic_values.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_symbolic_values.md), [`extract_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_disjunction_projection.md), [`extract_disjunction_projection_missing_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_disjunction_projection_missing_arm.md), [`a_bare_extract_between_execution_steps_adds_its_conjunct.md`](https://github.com/clicklang/click/blob/master/mdtests/a_bare_extract_between_execution_steps_adds_its_conjunct.md), [`extract_takes_an_implication_consequent_whole.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_takes_an_implication_consequent_whole.md)

### Context-free normalization

**Form:** `normalize()`

**Expansion output.** `click expand` writes it; by hand, write it to close a
goal that is true by evaluation alone, typically after `unfold` or `rewrite`.
It reads no facts, so it proves the same goal in every context.

**Accepts** a goal that is not itself a conjunction, disjunction, implication,
or quantifier, when evaluation makes it true:

- Every operation whose operands are all constants is evaluated: C machine
  arithmetic, bitwise operations, shifts, and division or remainder by a
  nonzero constant, all at the operand type's width; width and sign
  conversions, including `(uint64)` of an `int32` constant that `unfold` or
  `rewrite` substituted; exact `Integer` arithmetic and `to_integer` of a
  constant; and comparisons of constants.
- On symbolic terms, `x + 0`, `x - 0`, `x * 1`, and `x * 0` reduce, at C
  widths and for `Integer`.
- An equality, `<=`, or `>=` whose two sides are then the same term, up to
  renaming of bound variables, is true; so is `!=` between different
  constants.
- A `match` on a constructor selects its arm, and an equality between two
  applications of one algebraic constructor reduces to its fields.
- An equality or `!=` between sums and differences of C machine values, at
  32 and at 64 bits, compares the two sides' affine forms modulo 2^width:
  each side's terms are reordered, regrouped, and cancelled, and its
  constants combined. `x + y == y + x`, `x + (y + z) == (x + y) + z`,
  `x + y - y == x`, and `x - x == 0` are true, and `x + 1 != x` is true, for
  `int32`, `uint32`, `int64`, and `uint64` alike.
- A comparison (`==`, `!=`, `<`, `<=`, `>`, `>=`) between sums, differences,
  and negations of exact `Integer` terms compares their affine forms over the
  integers, with no modulus: when every term cancels, the constant difference
  decides it. `1 + to_integer(x) == to_integer(x) + 1`,
  `to_integer(x) - to_integer(x) == 0`, `a + b == b + a` for `Integer`
  parameters, `to_integer(x) + 1 != to_integer(x)`, and
  `to_integer(x) + 1 > to_integer(x)` are true. C machine order claims are not
  compared this way, since `x + 1 > x` is false at a type's maximum.

In both affine comparisons a term that is not a sum, difference, negation, or
constant, such as a product or a call, is one opaque operand, compared as a
whole.

**Outside it**, with what to write instead:

- A top-level `and`, `or`, implication, or quantifier: use `both`, prove one
  disjunct with `have` and close with `known()`, or `intro`.
- A goal that needs a fact, including a premise of the theorem: use
  `normalize() using { P; ... }`, `rewrite`, or `known()`.
- A pure function call: `unfold` it first; `normalize` leaves calls symbolic.
- Scaling or distributing, such as `2 * x == x + x`; an order claim between
  C machine sums, such as `x + 1 > x`; or an `Integer` order claim whose terms
  do not cancel, such as `to_integer(x) < to_integer(x) + to_integer(y)`: use
  `solve() using { ... }` or an arithmetic certificate.

**Failure, checking, and tools:**

A refusal prints the goal after substitution. Click runs the deterministic
leaf check; expansion is unchanged, and profiling charges the normalized
expression. Smart tactics retain the corresponding `both`, disjunct proof and
`known()`, or `intro` proof.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`normalize_evaluates_a_substituted_conversion.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_evaluates_a_substituted_conversion.md), [`normalize_compares_machine_sums_at_every_width.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_compares_machine_sums_at_every_width.md), [`normalize_compares_integer_sums_exactly.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_compares_integer_sums_exactly.md), [`normalize_does_not_scale_terms.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_does_not_scale_terms.md)

### Normalization with selected premises

**Form:** `normalize() using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, write it only in an
explicit proof that must evaluate a goal under named conditions without search.
It decides conditions in the goal from the cited premises and the equality
graph, then applies `normalize()`'s check (see
[Context-free normalization](#context-free-normalization)) to the result.

**Accepts** a goal that `normalize()` accepts after this reduction, when every
cited premise is accepted:

- A premise is accepted when it is available in the sense of `known()`'s
  atomic rules, or in its other polarity or direction, or holds without facts
  (`0 <= 0`), and it is a single condition or its negation: a comparison, an
  equality including an algebraic one, or its `not`. The list may be empty.
- Each condition in the goal, at any depth outside binders, including the goal
  itself, a conditional-expression guard, and a condition inside a
  pure-function argument, becomes `true` or `false` when a cited premise
  states it in any spelling: as written, at the other polarity (`x >= y` is
  `false` for a cited `x < y`), or mirrored (`y > x` for a cited `x < y`,
  `y != x` for a cited `x != y`), in every family (`int32`, the 64-bit
  machine types, and `Integer`).
- A condition is also decided when the equality graph built from the cited
  premises alone settles it: cited equalities are symmetric, transitive and
  congruent, so `x == y` decides `x + 1 == y + 1`, and `x < y` with `y == z`
  decides `x < z`.
- An equality condition between C machine values of either width, pointers,
  or pointer offsets becomes `true` when the ambient equality graph of all
  checked facts proves it, whether or not it is cited: `x == y` as a fact
  closes the goal `x + 1 == y + 1` under `normalize() using { }`. The graph
  supplies program values, such as loads, that a proof cannot always name;
  specification values (`Integer` and algebraic) are cited instead.
- A goal that compares a term with a constant closes when the cited
  conditions on that term decide it, in every family, the 8- and 16-bit
  types included: `a <= 5` or `a < 5` gives `a <= 10`, and `n == 0` gives
  `n != 1`.
- Two addresses in one block whose offsets differ, after their shared
  addends cancel, by two element indices on one side and one on the other at
  one element width are equal when a cited premise states the one index's
  exact `Integer` value as the sum of the other two, in either order or
  orientation: `(bytes + prefix) + suffix == bytes + total` from
  `to_integer(total) == to_integer(prefix) + to_integer(suffix)`, for every
  index type. One of the two may be a constant offset, a whole number of
  elements: `(bytes + prefix) + 3 == bytes + total` from
  `to_integer(total) == to_integer(prefix) + 3`. A native sum
  (`total == prefix + suffix`) does not, because it may wrap
  ([`normalize_using_adds_element_indices_by_a_cited_integer_sum.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_adds_element_indices_by_a_cited_integer_sum.md),
  [`normalize_using_adds_a_constant_element_offset_by_a_cited_integer_sum.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_adds_a_constant_element_offset_by_a_cited_integer_sum.md),
  [`normalize_using_refuses_a_wrapping_index_sum_for_an_address.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_refuses_a_wrapping_index_sum_for_an_address.md)).
- For a top-level read equality of any width, a pointer read equality, or a
  pointer-offset equality, the cited conditions can justify the read's
  recorded stored value or the offsets' equality directly, and for
  `defined(...)` of a read, that a store wrote its bytes; see the paragraph
  below.

**Outside it**, with what to write instead:

- A premise that is a conjunction, disjunction, implication, or quantifier:
  `extract` the single condition and cite it. Two premises stating opposite
  values of one condition are refused as inconsistent.
- A goal that needs a cited equality's value substituted into a term, such as
  `x * 2 < 15` from `x == 7`: `rewrite(x, 7)` then `normalize()`
  ([`normalize_using_decides_conditions_without_substituting.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_decides_conditions_without_substituting.md)).
- A goal between two symbolic terms that follows from a cited premise without
  being one of its spellings, such as `x <= y` from `x < y`:
  `solve() using`.
- An unlisted ambient order condition, or an ambient `Integer` or algebraic
  equality: cite it.
- A top-level conjunction, disjunction, or implication remaining after
  reduction: `both`, a disjunct `have`, or `intro`, as for `normalize()`.
- A condition inside a quantified body, a `match`-arm body, or a range-fold
  binder: `intro` or `unfold` it first. Pure calls stay symbolic.

**Failure, checking, and tools:**

A refusal names the first unavailable or unsupported premise by index, or
reports that the reduced goal did not normalize. Every cited premise is
validated, even if the graph already establishes the goal. An unsuccessful
graph query leaves equality unknown, never false.

Ambient equalities in the kernel graph include symbolic-pointer transitivity
and supported same-version-point load congruence, plus explicit pointer-offset
equality and addition congruence (including equal displacements of ordinary C
pointer parameters); explicit int32 equality, transitivity, and addition
congruence are also available, including propagation into same-width int32
scaled offsets. Registered four-byte int32 reads also have congruence at equal
offsets at the same version point and storage block.

A read of at most four bytes, and `defined(...)` of a read of any width, are
justified the same way: the walk, reading the cited conditions only, must end
at a store that writes the read's whole width, so `t[j + 1] = 0` under a
cited `j == 2` gives `t[3u64] == 0u8` and `defined(t[3u64])`
([`normalize_using_reads_a_narrow_stored_value.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_reads_a_narrow_stored_value.md),
[`normalize_using_refuses_a_narrow_value_the_store_did_not_write.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_refuses_a_narrow_value_the_store_did_not_write.md)).

For a top-level 64-bit read equality, the cited conditions can also justify
its recorded stored value: the typed memory-history walk checks each effect,
including the caller-owned ranges recorded by a call, and requires a complete
eight-byte value. The walk crosses at most 64 history edges; a longer frame
needs an explicit intervening proof step. An overwritten or partially
overwritten read cannot reuse the old value. This adds no ambient frame search
or read permission. Explicitly cited equality between the exact Integer
observations of a `uint64` index and an `int32` index also establishes equal
pointer offsets at one common element width, including common base
displacements. A low-word equality is insufficient, and equality does not
establish C signed definedness.

Expansion retains the normalization step and cited evidence; checking
reconstructs the graph from the surrounding checked proof context. Work
follows the selected expression and premises.

**Checked examples:** [`normalize_using.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using.md), [`normalize_using_graph_conditions.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_graph_conditions.md), [`normalize_using_rejects_ambient.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_rejects_ambient.md), [`normalize_using_decides_conditions_without_substituting.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_decides_conditions_without_substituting.md), [`uint64_int32_exact_index_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_exact_index_alias.md), [`uint64_int32_owned_index_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_owned_index_alias.md), [`uint64_int32_low_word_is_not_address_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_low_word_is_not_address_equality.md)

### Arithmetic search

**Form:** `solve() using {}`. The parser refuses the removed spelling
`arithmetic()` and names `solve() using {}`.

**Specialized.** Write it only for a bound that follows from the goal's own
terms, such as `(x & 255) <= 255`; it reads no fact. `solve() using {}` tries
the engine this section describes after its other closers, over no premises.
The engine plans and checks a bounded
arithmetic certificate for the current comparison or equality, in the signed
`int32` family or in the mathematical `Integer` linear family.

The family is decided by the goal's own checked terms, never guessed from its
spelling, and the two never coerce into each other. For `int32`, affine terms
plus bounded products and constant remainder, shift, and bit-mask terms are
supported. A `uint32` order goal is checked in the same family from its
operands' signed intervals, so explicit signed bounds `0 <= n` and
`n <= 536870911` give `(n as uint32) <= 1073741823u32`. A chain of `uint32`
order premises, such as `x < n` and `n <= 4u32` giving `x < 4u32`, is summed
over the operands' `uint32` observations in the `Integer` family, as a
`uint64` chain is.

For `Integer`, the goal is a linear comparison or equality over Integer atoms,
including opaque pure-function applications and range folds.

**Failure, checking, and tools:**

The bare form lists no premises and reads no fact from the context, so it proves
only what follows from the goal's own terms, such as `(x & 255) <= 255`; a goal
that depends on a fact needs the `using` form, and a failure says so. An
unsupported operator, a possibly overflowing goal expression, or a
nonconsequence fails locally.

A goal recognized as `Integer` linear reports that fragment, not the `int32`
precondition. The planner runs once and expansion retains its checked structural
certificate.

**Checked examples:** [`pure_arithmetic_affine.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_affine.md), [`pure_arithmetic_bounded_operations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_bounded_operations.md), [`arithmetic_on_an_unfold_refreshed_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_on_an_unfold_refreshed_goal.md)

### Arithmetic with selected premises

**Form:** `solve() using { P; ... }`. The parser refuses the removed spelling
`arithmetic() using { P; ... }` and names `solve() using { P; ... }`.

**Specialized.** Write it when `solve` misses an integer bound or equality,
listing the premises the bound follows from. `solve() using` tries the
engine this section describes last, and a miss adds the engine's reason
(`mdtests/a_solve_using_miss_reports_arithmetic_s_reason.md`). The engine
plans and checks a bounded
certificate using only the exact listed premises; no ambient fact participates,
and a listed premise outside the goal's family is skipped rather than refused.

In the signed `int32` family, summed inequalities have positive coefficients;
bounded nonlinear terms use interval facts; one selected premise can be scaled
to a larger coefficient. A selected affine machine premise can also be
decomposed when the listed bounds prove every operation defined: `a <= 1000 - b`
(or `a == 1000 - b`) with `1 <= b; b <= 1000` gives `a <= 999`, and `a + b <=
1000` gives the same bound when both operands have safe listed ranges.

Expansion records the premise conversion as `affine_premise source left_evidence
right_evidence => P;`, with checked interval evidence for both expression roots.
Premise conversion also composes with a compound goal: safe listed bounds and `a
<= 2147483646 - b` establish `1 + a <= 2147483647 - b`.

Every decomposed premise and goal operation has independent interval evidence
from the original listed facts; an affine consequence cannot justify its own
definedness. Also checks pointer alignment and equal byte translations of one
listed pointer equality, including `p + 1 == arr + (i + 1)` from `p == arr + i`
and `i < n`.

Signed index sums are distributed only when the listed scalar bounds exclude
overflow. A goal spelled `>` or `>=` is read from the other side, so a bound
over a machine operation is planned in either orientation. A listed non-strict
bound and a disequality on the same two sides give the strict bound, which the
certificate records as `less_than_from_not_equal`.

A strict bound `i < n` bounds `i` by `2147483646` through `n`'s own `int32`
range when no premise bounds `n`, which the certificate records as
`int32_range`; a non-strict `i <= n` bounds `i` only by `2147483647`. In the
`Integer` linear family, any number of listed equalities participate: they are
eliminated, in the order written, each solved for the smallest atom it still
mentions, with exact integer cross multiplication and no division. When those
bounded combinations miss an `Integer` bound, arithmetic refutes the goal's
negation from all the listed premises by simplex, so a chain of any length
closes; the certificate adds up the cited premises and the negated goal to a
constant contradiction.
When that refutation needs a value's type range, as `k < x` with `x == 0u64`
needs `0 <= to_integer(k)`, it retries with the type range of each machine
value the goal and listed premises observe, spelled from the written operand,
and the certificate cites each one it uses as a `type_range` bound. A `false`
goal is proved the same way, from the listed premises alone
([`arithmetic_using_reads_unsigned_type_ranges.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_using_reads_unsigned_type_ranges.md));
a signed value has no zero floor, so `k < x` with `x == 0` is consistent
([`arithmetic_using_signed_values_have_no_zero_floor.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_using_signed_values_have_no_zero_floor.md)).

An equality goal must reduce away completely; an order goal is decided, after
that elimination, by at most two of the reduced inequalities, whether or not the
elimination changed the goal itself. A `uint64` or `int64` order or equality
goal is first tried by the certificate families, which read each listed
comparison of that type as its Integer fact; when they miss, it is proved
through the exact Integer observations of its operands; one
written the other way round, `n >= i - 1` or `not (n < i - 1)`, is proved as
`i - 1 <= n` and closed from it. A comparison of observations is the native
comparison itself (see
[One form for comparisons of observations](../../internals/mathematical-integers.md#one-form-for-comparisons-of-observations)),
so each listed premise of that type is restated over its observations by
`known()`, a listed `not left < right` is read as `right <= left` and a
listed `right > left` as `left < right`, each value written beside a sum or
difference has its type's range stated by a `type_range` certificate (so `i -
1` is defined under `0 < i`), each sum and difference in the premises and the
goal is shown to stay in range from the facts before it, by both constant
bounds of its exact value, and observed by an `integer_operation_identity`
certificate citing those bounds, the Integer claim is proved in the `Integer`
family, and `known()` concludes the goal. A listed premise the proof does
not hold is refused as an unavailable exact premise.

An equality goal takes its type from a listed order premise or a typed literal,
and is read this way only when both sides are sums and differences of plain
operands; an equality over a product, a shift or a mask is left to the other
families. An unsigned sum must not exceed the type; a signed one is defined
once both Integer bounds of its exact value are facts, which together are its
definedness fact, so `known()` states it; a premise over a signed sum is
carried only once that sum is defined.

Expansion writes those steps out as `have` steps with their explicit
arithmetic certificates; none cites a standard-library theorem.

A disequality goal `a != b` (or `not (a == b)`) over machine or `Integer`
operands, which no certificate family reads directly, is proved by refuting
`a == b`: `intro()` adds the equality and leaves `false`, which arithmetic
proves from the listed premises and the equality. `k < j` gives `k != j`
([`arithmetic_proves_a_disequality_by_refuting_its_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_proves_a_disequality_by_refuting_its_equality.md));
`k <= j` does not, and the refusal is the one for the `false` goal
([`a_disequality_its_premises_allow_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/a_disequality_its_premises_allow_is_refused.md)).
`solve` proves `a < b`, or else `b < a`, by selected-premise arithmetic,
which a linear refutation of `a == b` always leaves, and refutes the equality
from it; its expansion writes that `have`, `intro()` and the certificate.

Arithmetic reads no disequality premise, so a disequality goal that only
another disequality gives is proved by cases. When every other strategy
misses, `solve` splits on `a == b` and, in that arm, proves `p == q` for an
available `p != q` connected to the goal (at most four, in turn), which
`known()` closes against the stated fact; the other arm holds the goal.
This carries the Integer fact `m - 1 != 0` to the `int32` word fact
`((m - 1) as int32) != 0` where the facts keep `m - 1` in range, and back.
It refuses where the word may wrap: `u + 1 != 0` over a `uint32` `u` does not
give `((u + 1) as uint32) != 0`
([`a_store_index_fact_may_be_the_integer_or_the_word.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_index_fact_may_be_the_integer_or_the_word.md),
[`an_integer_disequality_does_not_give_a_wrapping_word_one.md`](https://github.com/clicklang/click/blob/master/mdtests/an_integer_disequality_does_not_give_a_wrapping_word_one.md)).
Expansion writes the proof `if`, the `have p == q` with its certificate, and
the two `known()` steps.

After that, a pointer disequality between two element addresses of one
base, `&q[j] != &q[0]`, whose indices have one width and format (`int32`, or
64-bit of one signedness), is reduced to its indices: `solve` states
`have j != 0` (spelled from the index words, as the store search spells its
fact: `((m - 1) as int32) != 0`, `j != 0u64`), proves it by `solve`, and
closes the goal with
`apply(click::separation::distinct_elements(q, j, 0)) using { j != 0; }`.
Expansion writes that `have` and the `apply`. Where the indices may be equal
the nested `solve` misses and the goal's ordinary refusal stands
([`solve_proves_element_addresses_distinct_from_their_indices.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_element_addresses_distinct_from_their_indices.md),
[`solve_proves_element_addresses_distinct_at_each_index_type.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_element_addresses_distinct_at_each_index_type.md),
[`solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.md)).

**Failure, checking, and tools:**

A 64-bit sum or difference the listed premises do not keep in range is refused
by name: where it may leave the type's range it is not the sum or difference of
its operands. An unavailable premise, unsupported relation, possible goal
overflow, or failed consequence fails locally. An `Integer` refusal names that
fragment and lists which premises were read as `Integer` linear claims and which
were skipped.

A goal coefficient an elimination pivot does not divide also fails locally:
concluding a multiple of the goal is not concluding the goal, and no certificate
node divides that factor back out. The planner scans only explicit premises and
emits a flat certificate; expansion directly rechecks that certificate without
planning again.

**Checked examples:** [`pure_arithmetic_affine.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_affine.md), [`pure_arithmetic_bounded_operations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_bounded_operations.md), [`c_pointer_local_loop_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/c_pointer_local_loop_invariant.md), [`arithmetic_plans_a_greater_bound_on_an_operation.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_plans_a_greater_bound_on_an_operation.md), [`arithmetic_sharpens_a_bound_with_a_disequality.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_sharpens_a_bound_with_a_disequality.md), [`arithmetic_bounds_a_strict_lower_side_below_int32_max.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_bounds_a_strict_lower_side_below_int32_max.md), [`arithmetic_eliminates_integer_equalities.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_eliminates_integer_equalities.md), [`arithmetic_refuses_an_unchained_integer_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_refuses_an_unchained_integer_equality.md), [`a_size_t_loop_stepping_by_two_closes_with_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/a_size_t_loop_stepping_by_two_closes_with_arithmetic.md), [`a_uint64_sum_that_may_wrap_is_not_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/a_uint64_sum_that_may_wrap_is_not_arithmetic.md), [`arithmetic_proves_int64_order_goals.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_proves_int64_order_goals.md), [`an_int64_sum_that_may_overflow_is_not_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/an_int64_sum_that_may_overflow_is_not_arithmetic.md), [`arithmetic_reduces_order_premises_under_an_untouched_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_reduces_order_premises_under_an_untouched_goal.md), [`arithmetic_compound_premise_and_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_compound_premise_and_goal.md), [`arithmetic_compound_wrapping_premise.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_compound_wrapping_premise.md)

### Preservation

**Form:** `preserve(separate(region.footprint, resource));`

A simple tactic for a read-equality or read-definedness goal. Cite an exactly available separation
between a recorded region footprint and the resource being read. The tactic
constructs equality of the selected read at the region's exit and entry, in
that order. It applies one primitive directly, with no premise discovery or
history search. The current goal selects the read type or named-resource
field; it must match the constructed equality.

For `defined(read)`, the separated resource must be the complete typed cell.
The tactic looks up the exact `defined(read)` fact at the footprint's entry
and constructs it at the exit. The footprint supplies both points; the
separated cell supplies the address. Missing old definedness is a local refusal,
not a request to search memory history. This rule preserves definedness; it
does not establish initialization from ownership or value equality alone.

Use an ordinary `have` to establish this equality, then `rewrite` and
`known` to carry a proposition across the change. The tactic remains
`preserve(...)` in expansion. Unavailable separation, an unsupported observation,
or mismatched endpoints is a local refusal. This tactic is distinct from a
loop's `preserve by { ... }` proof block.

**Checked example:** [`preserve_step_carries_a_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_step_carries_a_fact.md).

`region.footprint` is a resource descriptor, not ownership. Execution records
writes, call effects, resource changes, and allocation lifetime changes while
producing the transition. Splitting or rejoining spatial ownership, or updating
an iterated ownership marker, does not modify memory bytes; named-resource
changes remain effects. A footprint can contain several resources and can
conservatively include more than the exact mutated cells. Selecting it uses
recorded region boundaries, never a memory-history search. A boundary without
a complete recorded effect sequence is refused.

For a call whose mutable effect comes from full owned resource inputs,
execution can publish `contains(R, region.footprint)` directly. `R` is the
checked caller-side resource selected for the call input, or their separating
conjunction in contract order. The producer retains those abstract resources
without unfolding their bodies. Borrowed and consumed inputs both count: the
call writes only memory they hand it, and a resource it produces is made from
them, so a produced output does not cancel the bound. After the call a
consumed instance is no longer held; name it as it was before the call with
`at(mark, name)`
(`mdtests/a_consumed_field_bearing_instance_bounds_the_call_footprint_at_a_mark.md`).
Non-unit quantities, construction, extra runtime effects such as allocation or
release, or additional unaccounted changes do not receive this bound. A one-transition
source selector names the same descriptor that the step published.

Use `known()` to select the published containment, then apply
`separation::contains_refl` and `separation::separate_restrict` with the explicitly
available resource separation. For several inputs, first use
`separation::separate_star`. The resulting footprint separation is an ordinary
premise of `preserve`; this route needs no footprint normalization.
See `mdtests/recursive_call_footprint_containment.md` and
`mdtests/recursive_call_pair_footprint_containment.md`.

For one checked transition, prove `separate(region.footprint, B)` with
`normalize() using { ... };`, listing an exact separation for each affected resource. Restrict parent
separations or rewrite aliases in preceding explicit proof steps. Spatial ranges
are compared in byte coordinates; their written range-validity conditions are
retained. Separating two footprint collections is not a simple normalization
rule. Empty memory ranges, distinct storage blocks, and token/memory pairs
are disjoint directly. This simple rule does not walk a region containing several transitions: write individual
`have` goals using `preserve(...)`, then compose the equalities with `rewrite` and `known`.

`preserve` supports complete pointer, `uint8`, 32/64-bit integer, and abstract
typed memory observations. It also preserves a selected field of a named owned
resource: cite `separate(region.footprint, r)` and write
`preserve(separate(region.footprint, r));` under a goal such as
`r.field == at(region.entry, r.field)`.
Field lowering supplies the instance identity and field selector. The primitive
reads that field from the footprint's persistent entry and exit resource contexts
by identity; it does not unfold the resource or enumerate its other fields.
Split expressions involving different resource fields into individual links.
Supported field values include algebraic values, mathematical `Integer`,
abstract C values, pointers, and the integer types listed above.
A byte read retains its one-byte storage extent even though C promotes its
equality to `int32`; separating one byte never licenses a four-byte read. The
result is oriented after-to-before. Logical read producers
retain their complete typed values under the exact version point, address, and read
type. `preserve` looks up the selected observations and constructs their equality;
it does not reconstruct values from cached cells or memory derivations. This
includes pointers whose address and provenance have different internal names.
Read observations are retained only while lowering and applying an explicit
`preserve(...)` step, then released. Nested applications have isolated tables. Ordinary
checking does not retain these observations. Missing observations fail locally;
no alias or history fallback runs.
Pointer preservation also accepts address equality when the pointer domains
already agree. Equality composition uses ordinary `rewrite` and `known` steps.
Footprints can record non-memory resources, symbolic release extents, and
multiple mutable call resources. Wide-index memory ranges are not yet supported.
Joined branch/loop footprints still need
producer integration; use recorded individual transitions where available.
An unavailable premise, unsupported rule, or mismatched endpoint fails locally.

**Checked examples:** [`preserve_pointer_read.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_pointer_read.md), [`preserve_resource_field.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_resource_field.md).

### Arithmetic certificates

Migration to ordinary arithmetic proofs has begun. These certificate rules
have named laws, applied with explicit `using` premises:

| Certificate operation | Ordinary law |
| --- | --- |
| Add two non-strict Integer bounds | `integer::add_le(a, b, c, d)` |
| Scale an inequality by a nonnegative factor | `integer::multiply_order_nonnegative(a, b, factor)` |
| Round an Integer upper bound | `integer::round_down_le(value, bound, divisor, remainder)` |

`solve() using` expands a direct sum of two selected non-strict Integer bounds
to `apply(integer::add_le(...)) using { ... }`. Other arithmetic still uses
the certificate forms below. The [library reference](../library/index.md#foundational-integer-order-axioms)
states the laws' exact guards. General affine composition, equality and
refutation plans, signed interval proofs, and specialized cast, pointer and
floating rules remain to migrate; their replacement is not implicit in `apply`.


**Form:** `arithmetic_certificate { premise ...; conclusion N; }` / `arithmetic_certificate signed_int32 { ... }` / `arithmetic_certificate rules { ... }`

**Expansion output.** `click expand` writes it; a person writes `solve()
using` instead and lets expansion produce the certificate. Check a typed
arithmetic-certificate envelope against the current goal; it closes the goal
or refuses.

**Accepts** a certificate whose every line its family's checker recomputes,
under these envelope rules common to the three forms:

- Exactly one `conclusion N;` names a node by its position, counting from 0
  in written order. Every node reference names an earlier node.
- `premise i: P => R;` imports the cited proposition `P`, which must be
  exactly available: a fact or leaf conjunct, or decided by the equality
  closure, written in the fact's own direction. Premise indices are
  contiguous from 0.
- In the unsuffixed and `signed_int32` forms each `premise` line is itself a
  node, and `R` states the claim it contributes. In `rules`, `premise` lines
  are numbered separately, are not nodes, must repeat `P` token for token as
  `R`, and nodes cite them by premise index (`bounds [i, j]`,
  `premise i`).

**The unsuffixed form** is the mathematical `Integer` family:

- The goal is a linear comparison `<`, `<=`, `==`, `>=` or `>` over Integer
  atoms (variables, products of atoms, pure-function applications, range
  folds, and machine observations `to_integer(v)`), or a native machine
  comparison, read through its operands' exact observations.
- Each claim is normalized to `t <= 0` or `t == 0` with integer coefficients;
  `a < b` is `a - b + 1 <= 0`. A node's `R` may use any spelling with that
  normal form.
- Nodes: `premise`; `scale i by c` (`c >= 0` for a bound, any constant for an
  equality); `add i, j` of two claims of one relation; `less_equal_from_equal
  i` and `less_equal_from_equal i reverse`; `equal_from_bounds i, j` from
  opposite bounds, stated in node `i`'s orientation; `trivial` (a claim with
  no atoms left, such as `x + 1 > x`); `type_range` (`MIN <= to_integer(v)` or
  `to_integer(v) <= MAX` for a machine `v`); `operation_bound` (the bound a
  quotient, shift, or remainder by a positive constant takes from its
  operand: `c * to_integer(x / c) <= to_integer(x)`, `to_integer(x) <= c *
  to_integer(x / c) + (c - 1)`, `to_integer(x % c) <= c - 1`, with `x >> k`
  as `x / 2^k`; for a signed `x / c`, `c * to_integer(x / c) - (c - 1) <=
  to_integer(x)` in place of the first, and `-(c - 1) <= to_integer(x % c)`);
  `excluded_bound N: D` (premise `N`, a disequality `v != MIN` or `v != MAX`
  of a machine `v`, as `MIN + 1 <= to_integer(v)` or `to_integer(v) <= MAX -
  1`) ([`operation_and_excluded_bounds_in_an_arithmetic_certificate.md`](https://github.com/clicklang/click/blob/master/mdtests/operation_and_excluded_bounds_in_an_arithmetic_certificate.md),
  [`an_operation_bound_must_be_the_exact_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/an_operation_bound_must_be_the_exact_bound.md));
  `less_than_from_not_equal i, N: D` (node `i`, a non-strict bound `t <= 0`,
  made strict, `t + 1 <= 0`, by premise `N`, a disequality `l != r` whose
  difference `l - r` is `t` or `-t`; `solve` adds it only after the linear
  facts leave a counterexample, at every format and over `Integer`,
  [`a_bound_and_a_disequality_give_a_strict_64_bit_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/a_bound_and_a_disequality_give_a_strict_64_bit_bound.md)); `negated_goal` (the integer
  negation of a bound goal); `divide i by g` (a non-strict bound by a positive
  common factor of its coefficients, rounding its constant).
- The conclusion node's claim equals the goal's, or is a contradiction such
  as `1 <= 0`, which proves any supported goal
  ([`integer_certificate_refutation_and_rounding.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_certificate_refutation_and_rounding.md)).
- A premise comparing exact observations of one machine type is also
  available from its native comparison, and an Integer bound of a signed
  result from the corresponding definedness fact.

**`signed_int32`** is checked signed-machine arithmetic over 32-bit words:

- Affine nodes `premise`, `scale`, `add`, `less_equal_from_equal`,
  `equal_from_bounds`, `less_than_from_not_equal` (a non-strict bound and a
  disequality on the same form give the strict bound), `trivial`, and
  `int32_range` (an opaque atom's `int32` range).
- Interval nodes that establish an operation's range and definedness:
  `interval_from_affine`, `interval_from_affine_direct`, `interval_atom`,
  `defined`, `interval_intersect`, `interval_add`, `interval_add_bounded`,
  `interval_subtract`, `interval_multiply`, `interval_remainder`,
  `interval_remainder_add`, `interval_shift_left`,
  `interval_arithmetic_shift_right`, `interval_bitwise_and`,
  `interval_compare` (whose `ult` and `ule` comparisons conclude a `uint32`
  order from the operands' signed intervals once each has a known sign,
  [`a_signed_certificate_concludes_a_uint32_order_from_intervals_of_known_sign.md`](https://github.com/clicklang/click/blob/master/mdtests/a_signed_certificate_concludes_a_uint32_order_from_intervals_of_known_sign.md)),
  and `interval_narrowed_cast`,
  which treats a C conversion into `int8`, `uint8`, `int16` or `uint16` of a
  32-bit-word operand as that operand when the operand's checked interval
  lies inside the destination range
  ([`a_conversion_in_range_is_its_operand_in_a_signed_certificate.md`](https://github.com/clicklang/click/blob/master/mdtests/a_conversion_in_range_is_its_operand_in_a_signed_certificate.md)).
- `affine_premise`, `affine_conclusion`, and `affine_conclusion_pair`, which
  decompose an affine machine premise or goal with interval evidence for
  every operation root.
- The conclusion node's claim equals the goal's affine claim; two trivially
  true constant comparisons on one carrier also match.

**`rules`** checks one named rule per node, and the conclusion node's result
must be the goal itself:

- `pointer_translation`, `pointer_alignment`, `pointer_word_equality`, and
  `pointer_word_from_alignment` for pointer translation, alignment and
  tagged words; `float_reflexive` for a finite float; `unsigned_sum_bound`.
- `int64_defined bounds [i, ...] => defined(a + b);` (or `a - b`) proves
  `int64` definedness: each operand's range is the width range of its root
  constructor (a constant, or a value widened from `int` or `unsigned int`;
  any other `int64` term has the whole `int64` range), narrowed by the listed
  premises, each a constant `int64` order or equality fact on an operand, and
  the exact result range must stay inside `int64`. `int32_defined` is the
  same checker at `int32`: a constant operand is itself and any other `int32`
  term (including a promoted `char` or `short`) has the whole `int32` range,
  and the listed premises are constant `int32` facts.
- `integer_product_bounds bounds [i, j, k, l] => T <= x * y;` (or `x * y <=
  T`) uses four constant-endpoint bounds in left-lower/upper then
  right-lower/upper order; see the product-bound rule below.
- `integer_division_bounds bounds [i, j, k, l] => T <=
  truncating_quotient(n, d);` (or an upper bound, or `truncating_remainder`)
  checks four explicit constant-endpoint numerator/divisor bounds and requires
  the divisor interval to exclude zero; see [division
  bounds](../../internals/mathematical-integers.md#truncating-division-bounds).
- `integer_quotient_bound bounds [i, j] => b <= truncating_quotient(n, d);`
  (or an upper bound) checks the exact scaled numerator bound followed by
  `1 <= d`; see [scaled quotient
  bounds](../../internals/mathematical-integers.md#scaled-positive-divisor-quotient-bounds).
  `integer_bound_exclusion bounds [i] => x != c;` excludes a constant
  strictly outside one named non-strict bound; see [bound
  exclusion](../../internals/mathematical-integers.md#bounds-excluding-constants).
- `integer_polynomial_identity bounds [] => L == R;` checks a bounded
  mathematical Integer ring identity with non-ring roots opaque;
  `integer_quotient_shift bounds [i, j] => truncating_quotient(x + d * k, d)
  == truncating_quotient(x, d) + k;` requires a positive constant divisor and
  exact named nonnegative bounds on `x` and `k`; see [polynomial and quotient
  rules](../../internals/mathematical-integers.md#bounded-polynomial-identities-and-quotient-shifts).
- `integer_relation_transport bounds [i, j] => P;` uses a named Integer
  equality to replace one whole operand of a named equality or non-strict
  bound; it checks relation kind, polarity, and operand identities without
  recursive substitution.
- `integer_cast_identity bounds [i, j] => to_integer(cast_value) ==
  to_integer(source_value);` checks two named bounds against the typed cast
  destination's range; see [the cast identity
  rule](../../internals/mathematical-integers.md#range-checked-modulo-cast-identities).
  Unsigned byte and 16-bit readbacks with canonical low-bit masks retain
  their observations when promoted to a 32-bit word; both source bounds
  remain explicit. The Integer-to-machine conversion is read the same way:
  `integer_cast_identity bounds [i, j] => to_integer(to_T(z)) == z;` with
  `z`'s two bounds inside `T`'s range, at every format, which `solve` plans
  ([`an_integer_converted_to_a_machine_type_reads_back.md`](https://github.com/clicklang/click/blob/master/mdtests/an_integer_converted_to_a_machine_type_reads_back.md)).
- `integer_operation_identity bounds [i, j] => to_integer(a + b) ==
  to_integer(a) + to_integer(b);` (or `-`, `*`) checks two named constant
  bounds on the Integer result against the range of the operation's format,
  8 to 64 bits; see [in-range sums, differences and
  products](../../internals/mathematical-integers.md#in-range-machine-sums-differences-and-products).

**Outside it**, with what to write instead:

- A premise that is not exactly available, including an `Integer` fact
  cited in the opposite direction (`3 >= x` for the fact `x <= 3`): cite it
  as the fact is spelled, or prove it with `have` first.
- An `Integer`-family goal `x != c`: `integer_bound_exclusion` in `rules`.
  `negated_goal` of an equality goal: two bound certificates and
  `equal_from_bounds`.
- A negative `scale` of a bound: scale the opposite bound, or derive it from
  an equality.
- A conclusion stronger or weaker than the goal (`a < b` for the goal
  `a <= b`): add the remaining `trivial` and `add` nodes, since the claim must
  equal the goal's.
- A contradiction as the conclusion of a `signed_int32` or `rules`
  certificate: only the unsuffixed form accepts one.
- A node of another family, or a proposition at another point or inside a
  conjunction: a separate `have` step for each family, and `at(...)` or
  `extract(...)` steps for provenance; certificate families never coerce one
  another's propositions.

**Failure, checking, and tools:**

Every result is recomputed, references are bounded by the explicit
premise/node lists, and the first rejected node is named by index. An
`int32_defined` or `int64_defined` refusal names the result range found. Explicit certificates never
invoke planning or the legacy whole-goal checker. Machine families have no
implicit coercion between signed, unsigned, pointer, and float terms: source
conversions must be present and checked. Expansion emits the same certificate
that `verify`, `profile`, and `audit` inspect, so all four tools agree on the
checked proof.

**Checked examples:** [`arithmetic_certificate_surface.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_certificate_surface.md), [`integer_certificate_refutation_and_rounding.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_certificate_refutation_and_rounding.md), [`signed_int32_arithmetic_certificate_surface.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_int32_arithmetic_certificate_surface.md), [`signed_int32_certificate_composition.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_int32_certificate_composition.md), [`aligned_explicit_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/aligned_explicit_arithmetic.md), [`tagged_pointer_explicit_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/tagged_pointer_explicit_arithmetic.md), [`int64_defined_from_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/int64_defined_from_bounds.md), [`int32_defined_from_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/int32_defined_from_bounds.md), [`integer_product_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_product_bounds.md), [`integer_division_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_division_bounds.md), [`integer_cast_identity_unsigned_subword_promotion.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_cast_identity_unsigned_subword_promotion.md), [`an_in_range_machine_difference_is_its_integer_difference.md`](https://github.com/clicklang/click/blob/master/mdtests/an_in_range_machine_difference_is_its_integer_difference.md)

### Rewriting

**Form:** `rewrite(from, to)`

**Core.** Replace `from` with `to` throughout the current goal, using an
available equality `from == to`. The goal becomes the rewritten proposition;
no fact changes. Both arguments are expressions, not a proposition or a named
fact. Write `rewrite(x, y)`; the old `rewrite(x == y)` form is refused.

**Accepts** expressions `L` and `R` whose equality `P` is `L == R`, and a goal containing `L`:

- `P` is available: a fact or a leaf conjunct of one, or decided by the
  equality closure (`x == z` from `x == y` and `y == z`; `x + 1 == y + 1`
  from `x == y`), in either orientation: `rewrite(y, x)` is accepted
  from the fact `x == y`. `L == L` is accepted and changes nothing.
- `P` is a native equality of any C integer type (`int8` through `uint32`
  as 32-bit words, `int64` and `uint64` at full width), a mathematical
  `Integer` equality, a pointer equality, or an algebraic equality.
- Direction is as written: every occurrence of `L` is replaced by `R` in one
  pass, and `R` is not rewritten again. An occurrence is a subterm identical
  to `L` as lowered: C and `Integer` arithmetic associate to the left, so
  `rewrite(x + y, z)` rewrites `x + y + w` but `rewrite(y + w, z)` does not
  ([`rewrite_replaces_only_a_parsed_occurrence.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_replaces_only_a_parsed_occurrence.md)).
  `L` may be composite, such as `x + y` or a pure-function application.
- Occurrences are replaced under `and`, `or`, `not`, and implications; inside
  quantified bodies whose binder `P` does not mention; in conditional
  expressions' guards and arms; in pure-function arguments; in
  algebraic-constructor fields; under `to_integer` and width conversions such
  as `x as int64`; and in memory-resource ranges. Native equalities preserve
  signed and unsigned comparison kinds and widths, including full-width
  64-bit order.
- An `Integer` equality also rewrites a native comparison goal through its
  operands' exact observations: `to_integer(x) == to_integer(y)` and the goal
  `x < n` give `y < n`. It substitutes exact occurrences inside products,
  sums, negations, differences, truncating quotient/remainder terms and
  pure-function arguments; an exact whole-fold occurrence is replaced.
- A mathematical equality over observations of one 32- or 64-bit width and
  `+`, `-`, `*`, or negation also rewrites the corresponding machine terms:
  equality implies equality modulo that width. This direction requires no
  range premise and does not turn a machine equality into an Integer one.
  The conversion is bounded to 64 nodes in the cited equality.
- A pointer equality rewrites the base of an explicit `viewable(...)` claim
  while preserving the point it is stated at and its byte extent. A cited shifted view
  whose extent is `(i + 4) - i` also covers the same address with a literal
  four-byte extent; constant endpoint differences are compared in the
  extent's own modular arithmetic.
- A pointer equality also rewrites the addresses of loads read through the
  pointer, including byte reads observed with `to_integer` and a pointer that
  is itself loaded (`o->in->cells[2]` under `o->in == a`); it keeps the read's
  version point and load type. An equality whose left side is a whole
  symbolic pointer (`p == q`, `p == 0`) replaces that pointer everywhere,
  including inside `p as uint64`; null's address is the integer zero.
- Rewriting the word inside an integer-derived pointer rebuilds the pointer
  in the cast's canonical form. If the rewritten address is constant zero,
  it becomes null, with any byte displacement preserved. Thus rewriting a
  stored tagged word to `1` lets `normalize()` close its cleared pointer's
  equality to null
  ([`a_rewritten_tagged_null_pointer_normalizes.md`](https://github.com/clicklang/click/blob/master/mdtests/a_rewritten_tagged_null_pointer_normalizes.md)).
- When exact substitution misses an atomic native equality goal, its two
  operands may match `L` through checked corresponding read leaves, for both
  32-bit and 64-bit reads inside matching arithmetic operators. Alias and
  version-point evidence comes from the shared read-equality checker; incompatible
  read kinds, changed cells, and differing operators do not match. This
  comparison visits only `L` and the two goal operands.

**Outside it**, with what to write instead:

- A proposition that is not an equality (`x != y`, `x <= y`): there is no
  substitution by order; use `solve() using` or `normalize() using`.
- An equality available only as an implication's consequent: `extract` it
  first.
- A goal without an occurrence of `L`, including a different association or
  a constant that lowering folded away: rewrite by the equality as the goal
  spells it, or in the other direction.
- A quantifier that binds a variable of `P`: that subtree is left unchanged,
  and if nothing else changes the step is refused; `intro` first.
- An `Integer` equality under an internal fold or match binder, and an
  integer equality with a composite left side under the binder of a `match`
  arm: `unfold` or `match` first. An unfolded `match` the rewrite cannot
  enter is left exactly as it was.
- Rewriting a fact rather than the goal: rewrite a goal that restates it,
  then close with `known()`.

**Failure, checking, and tools:**

An unavailable equality, a missing occurrence, a blocked binder, or an
ill-typed rewrite fails, naming the equality as lowered beside the goal.
Click performs that rewrite only; expansion is unchanged, and profiling
charges the affected expression.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`equality_rewrite_scalar_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/equality_rewrite_scalar_bounds.md), [`integer_equality_rewrite.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_equality_rewrite.md), [`algebraic_symbolic_values.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_symbolic_values.md), [`rewrite_through_a_loaded_pointer_field.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_through_a_loaded_pointer_field.md), [`rewrite_pointer_inside_integer_read.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_inside_integer_read.md), [`rewrite_pointer_null_into_an_address.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_null_into_an_address.md), [`rewrite_pointer_into_a_shifted_byte_view.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_into_a_shifted_byte_view.md), [`rewrite_keeps_a_match_it_cannot_substitute_through.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_keeps_a_match_it_cannot_substitute_through.md), [`rewrite_replaces_only_a_parsed_occurrence.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_replaces_only_a_parsed_occurrence.md)

### Introducing a binder or premise

**Form:** `intro()`

**Core.** For an implication, negation, or universal goal, add the antecedent or
named binder and continue with the body goal. A universal's variable keeps the
name its quantifier wrote; if that name is already in scope it shadows the older
one, which stays readable as `outer.name`. That includes a range quantifier's
variable in a `have` stated between C statements
([`intro_names_a_range_variable_in_a_have_between_statements.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_names_a_range_variable_in_a_have_between_statements.md)).

**Accepts** a goal whose lowered head is one of these, and makes one
introduction:

- `A implies B`: `A` becomes a fact and the goal is `B`. A conjunction `A` is
  available conjunct by conjunct, so `known()` closes `0 <= k` after
  introducing `0 <= k and k < n`. `implies` groups to the right, so
  `A implies B implies C` takes two `intro()`s.
- `forall (x: T) { B }` for an `int32`, `uint64`, pointer, `Integer`, or
  `spec enum` binder: `x` is a new variable in scope and the goal is `B`.
- `(lo..hi).all(|x| { B })`: the first `intro()` binds `x`; the second adds
  the range guard `lo <= x and x < hi` as a fact and leaves `B`.
- An implication lowering inserted in front of a written body: the definedness
  of an operation the body evaluates, such as `defined(k + 1)` for
  `k + 1 > 0`, or a path fact. It is introduced as a fact while the written
  goal stays focused, so a written `forall (k: int32) { k + 1 > 0 and k >= 0
  implies k >= 0 }` takes three `intro()`s: binder, guard, antecedent.
- `not P` whose `P` lowers to a connective or quantifier, such as
  `not (A and B)` or `not (forall (x: int32) { ... })`: `P` becomes a fact and
  the goal is `false`, closed by `contradiction`.
- `not P` for a comparison or `bool` `P`, written as `not`, such as
  `not (n == 1)` or `not (x >= y)`, though lowering states it as one
  comparison: `P` becomes a fact and the goal is `false`.
- A disequality `a != b`, the negation of `a == b`, in every family:
  `a == b` becomes a fact and the goal is `false`.

**Outside it**, with what to write instead:

- An order comparison not written as `not`, such as `x < y`: `intro` does not
  turn it into a refutation of `x >= y`. Prove it directly, or split with a
  proof `if` or `cases` on the complement.
- A conjunction: `both`. A disjunction: prove one disjunct with `have` and
  close with `known()`.
- An existential, including `(lo..hi).any(...)`: `witness`.
- A comparison or other leaf: `normalize`, `solve() using`, `known`, or
  another closer.

**Failure, checking, and tools:**

A refusal names the goal's shape, such as "got a condition fact" or "got a
conjunction". Click checks the one introduction rule; expansion is unchanged,
and profiling charges one leaf.

**Checked examples:** [`copy_n_segment_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/copy_n_segment_invariant.md), [`quantifier_intro_nested_connectives.md`](https://github.com/clicklang/click/blob/master/mdtests/quantifier_intro_nested_connectives.md), [`lowering_guard_before_written_implication.md`](https://github.com/clicklang/click/blob/master/mdtests/lowering_guard_before_written_implication.md), [`integer_forall_intro.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_forall_intro.md), [`an_introduced_variable_hides_a_parameter_of_its_name.md`](https://github.com/clicklang/click/blob/master/mdtests/an_introduced_variable_hides_a_parameter_of_its_name.md)

### Naming an introduced binder

**Form:** `intro() as name`

**Specialized.** Write it when the quantifier's own variable name would clash
with or obscure a name the proof uses. For a goal written `forall (x: T) { ...
}` or `(lo..hi).all(|x| { ... })`, introduce the bound variable under `name`
instead of `x`, and continue with the body goal written in terms of `name`.

The proof chooses its own name where bare `intro()` takes the one the
proposition was written with.

**Accepts** exactly the universal goals bare `intro()` accepts, for every
binder type it accepts, when `name` is new:

- `name` is not a theorem or function parameter, C local, or earlier proof
  binding, including a variable an earlier `intro` introduced. The
  quantifier's own variable name, the name of a binder nested inside the
  body, and the name of a pure function do not count as in scope.
- A fact named by `have name: P` is hidden, not refused: `name` reads the
  variable for the rest of the block, and the fact stays available by its
  proposition.
- After a range quantifier's variable, the next `intro()` introduces its
  range guard; after a binder whose body lowering guarded, the next `intro()`
  introduces that guard.

**Outside it**, with what to write instead:

- A name already in scope: choose another; nothing is shadowed.
- An implication or negation goal, which introduces a fact, and facts have no
  names: write `intro();`, and cite the fact by its proposition.

**Failure, checking, and tools:**

A name clash is refused with "`name` is already in scope here; choose a name
that is not". Click checks the same one introduction rule; expansion is
unchanged.

**Checked examples:** [`intro_as_names_the_introduced_variable.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_names_the_introduced_variable.md), [`intro_as_requires_a_new_name.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_requires_a_new_name.md), [`intro_as_names_a_range_quantifier_variable.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_names_a_range_quantifier_variable.md), [`intro_as_on_a_range_quantifier_refuses_a_name_in_scope.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_on_a_range_quantifier_refuses_a_name_in_scope.md), [`intro_as_names_only_a_universal.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_names_only_a_universal.md), [`intro_as_hides_a_fact_name.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_hides_a_fact_name.md)

### Finite enumeration

**Form:** `enumerate()`

**Expansion output.** `click expand` writes it; by hand, write it only to close
a constant-bounded universal from instances you state one by one, or that
evaluate to true.

**Accepts** a goal `forall (k1: T1) { ... forall (kn: Tn) { B } }`, a chain of
one or more `int32` or `uint64` binders (a range quantifier `(lo..hi).all`
with constant `lo` and `hi` is one), when:

- `B` is an implication, or a conjunction of implications, and each one's
  antecedent bounds every binder it mentions to constants through its own
  conjuncts: `0 <= k`, `k < 4`, `k <= 1`, and the mirrored and negated
  spellings (`k >= 0`, `3 > k`, `not (k >= 3)`); a `uint64` binder with no
  lower bound starts at zero. The range of each binder is the hull over the
  implications that mention it.
- Each instance, at every point of that range in order, is discharged
  structurally with no search: an instance that is an available fact as
  written; a conjunction, conjunct by conjunct; an implication whose guard
  folds to false (vacuous) or to true with its conclusion discharged; or a
  leaf that evaluates to true with no facts, as `normalize()` would close it.
- A range with no member (`k < 0`, `k < 0u64`) has no instance to check.

**Outside it**, with what to write instead:

- A bound that is not constant, such as `k < n`, or a missing bound, such as
  an `int32` binder with only `k < 3`: `intro()` the binder and guard and
  prove the body.
- A guard written as an equality or a disjunction, such as `k == 2 implies`
  or `k == 2 or k == 3 implies`: restate it with order bounds, or `intro` and
  split cases.
- An `Integer` or pointer binder: `intro`.
- An antecedent conjunct that does not fold to a constant, such as `n > 0`
  beside the bounds: each instance must then be held whole, as written; or
  `intro` and prove the body.
- An instance held only in another spelling (`0 == f(0)` for `f(0) == 0`) or
  only derivable from facts: state it first with `have`.
- An instance that is a disjunction or is itself quantified, from an `or`
  between guarded bodies or a `forall` after an implication: hold each such
  instance whole with `have`, or `intro` and prove the body.

**Failure, checking, and tools:**

"requires a universal goal with constant bounds" means no constant table was
found; "requires each in-range instance as an exact available fact" means some
instance failed; neither names the instance. Click checks the finite table
with work proportional to it, one unit per instance, so a table beyond the
simple-tactic work budget (about 750,000 instances) exhausts it; expansion is
unchanged, and profiling reports that work.

**Checked examples:** [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`loop_entry_guard_intro.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_entry_guard_intro.md), [`enumerate_closes_instances_by_evaluation_or_exact_facts.md`](https://github.com/clicklang/click/blob/master/mdtests/enumerate_closes_instances_by_evaluation_or_exact_facts.md), [`enumerate_refuses_an_instance_held_in_another_spelling.md`](https://github.com/clicklang/click/blob/master/mdtests/enumerate_refuses_an_instance_held_in_another_spelling.md)

### Contradictions

**Form:** `contradiction(P)`

**Core.** Close the focused branch, whatever its goal, from `P` and its
negation. Nothing is searched: each check below is an indexed lookup or at most
one context-free normalization.

**Accepts** `P` when both halves hold:

- `P` is held: it is an available fact in any of its spellings (written,
  mirrored, such as `0 > x` for `x < 0` or `3 == x` for `x == 3`, or at the
  other polarity), possibly as a conjunct of a held conjunction; or `P` is a
  conjunction whose conjuncts are each available.
- Its negation is held: `not P` is an available fact; or `P` is a comparison
  and the opposite comparison of the same operands is (`x != 3` for
  `x == 3`, `x >= 0` for `x < 0`, `x <= 5` for `x > 5`); or one of the fixed
  equivalent spellings of its negation is, including the mirrored one
  (`0 <= x` for `x < 0`, `5 >= x` for `x > 5`, `3 != x` for `x == 3`), in
  every family: `int32`, the 64-bit machine types such as `x < 32u64` beside
  `x >= 32u64`, and `Integer`; or `not P` evaluates to true by
  `normalize()`'s rules, as for `P` = `1 == 0`, `x < x`, or
  `to_integer(x) + 1 == to_integer(x)`.
- `P` may be any proposition for the `not P` form, including a `bool`, a call
  comparison, an implication, or a quantifier.

**Outside it**, with what to write instead:

- A merely contradictory pair that is not a negation, such as `x < 0` beside
  `x >= 1`, or `x == 3` beside `x == 0`: first derive the negation with
  `have x >= 0 by solve() using { x >= 1; };`, or close with
  `solve() using { ... }`.
- A `not P` that needs scaling or overflow reasoning, such as `2 * x == x + x`
  or `x + 1 > x` at a C width: `solve() using { ... }`.

**Failure, checking, and tools:**

A refusal says which half is missing: "`P` itself is not an available fact", or
"`P` is available, but neither `not (P)` nor its opposite comparison is".
Expansion is unchanged, and profiling charges one leaf.

**Checked examples:** [`an_antecedent_normalization_refutes_closes_its_implication.md`](https://github.com/clicklang/click/blob/master/mdtests/an_antecedent_normalization_refutes_closes_its_implication.md), [`surface_syntax.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/surface_syntax.rs),
[`contradiction_opposite_comparison.md`](https://github.com/clicklang/click/blob/master/mdtests/contradiction_opposite_comparison.md),
[`uint64_branch_negation_refutes_the_other_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_branch_negation_refutes_the_other_arm.md), [`function_match_arm_closes_by_contradiction_after_a_have.md`](https://github.com/clicklang/click/blob/master/mdtests/function_match_arm_closes_by_contradiction_after_a_have.md), [`function_match_arm_contradiction_needs_a_refuted_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/function_match_arm_contradiction_needs_a_refuted_fact.md)

### Universal instantiation

**Form:** `instantiate(F, value)`

**Specialized.** Write it to use a universal fact at one value when `solve` does
not choose that value. Specialize universal fact `F` at `value` and add the
conclusion. The guards are fixed by `F` and `value`, so this is one
availability lookup per guard conjunct; nothing is unfolded or searched.

**Accepts** `F` and `value` when:

- `F` is an available fact, possibly a conjunct of a held conjunction, as
  written or with its binder renamed, and is `forall (k: T) { ... }` for `T`
  `int32`, `uint64`, `Integer`, or a pointer type such as `int32*`, or a
  range quantifier `(lo..hi).all(|k| { ... })` over `int32` or `uint64`.
- `value` is an expression of the binder's type: an `int32` C expression for
  an `int32` binder; a `uint64` one, such as `3u64` or `u`, for a `uint64`
  binder; an `Integer` expression, such as `5` or `to_integer(x)`, for an
  `Integer` binder; a pointer of the binder's type, such as a parameter or
  `result`, for a pointer binder.
- The guards are the conjuncts of the leading implications of `F`'s body at
  `value` (`A implies B implies C` has guards `A` and `B`; a range
  quantifier's guard is `lo <= value and value < hi`). A guard conjunct that
  evaluates to true needs nothing. Every other conjunct is available through
  the shared equality-backed lookup: as written, in an equivalent operand
  spelling (`x >= 0` for `0 <= x`, `n > x` for `x < n`), or through an
  equality fact (`0 <= y` and `x == y` give `0 <= x`).
- The conclusion is the rest of the body, which may itself be a universal,
  so a nested `forall` is instantiated one binder per step. An unguarded `F`
  needs no fact at all. If the conclusion is the goal, the goal closes
  unless other written steps follow.

**Outside it**, with what to write instead:

- A guard that only follows from facts, such as `0 <= x` from `1 <= x`: list
  those facts with `instantiate(F, value) using { 1 <= x; ... }`, or prove
  the guard first with `have`.
- An `int32` literal for a `uint64` binder (`3`): write `3u64`.
- `F` not available, or available only in a different spelling of its body:
  state it first with `have`.

**Failure, checking, and tools:**

An absent `F` fails with "`instantiate` quantified fact is not exactly
available"; an unavailable guard fails naming it ("missing exact guard: ...");
a value of the wrong type fails with "`instantiate` argument did not evaluate
to int32" (or uint64, or a pointer), and a pointer of another type with "the
argument is not a value of the universal binder's type". The conclusion is
the substituted body, constructed directly. Expansion is unchanged, and
profiling charges the guards and result.

**Checked examples:** [`instantiate_without_using_finds_its_guards.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_without_using_finds_its_guards.md), [`instantiate_without_using_names_a_missing_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_without_using_names_a_missing_guard.md), [`a_uint64_universal_is_not_instantiated_at_an_int32.md`](https://github.com/clicklang/click/blob/master/mdtests/a_uint64_universal_is_not_instantiated_at_an_int32.md), [`pure_theorem_instantiate.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_theorem_instantiate.md), [`instantiate_takes_an_integer_binder_at_a_literal.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_takes_an_integer_binder_at_a_literal.md), [`instantiate_takes_an_integer_binder_at_to_integer.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_takes_an_integer_binder_at_to_integer.md), [`instantiate_takes_a_pointer_binder.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_takes_a_pointer_binder.md), [`instantiate_takes_integer_and_pointer_binders_in_a_function_proof.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_takes_integer_and_pointer_binders_in_a_function_proof.md), [`instantiate_without_using_names_a_missing_integer_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_without_using_names_a_missing_integer_guard.md)

### Instantiation with selected premises

**Form:** `instantiate(F, value) using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which finds its guards. Specialize universal fact `F` at `value`, discharge its
guards from the listed premises and their checked machine readings, and add
the conclusion.

**Accepts** what the bare form accepts for `F`, `value`, and the conclusion,
with the guards discharged differently:

- Each listed `P` is an available fact, as written, in an equivalent operand
  spelling, or as a conjunct of a held conjunction.
- Each guard conjunct evaluates to true, equals a listed premise or a
  conjunct of one, is a polarity or operand respelling of one, or is derived
  from the listed premises alone by the checker's order and equality rules:
  `1 <= x` gives `0 <= x`; `x < y` and `y <= n` give `x < n`; `x == y` and
  `0 <= y` give `0 <= x`.
- A listed Integer comparison over a machine addition or subtraction can
  supply its native guard when exact indexed range facts in the proof context
  establish that the operation does not wrap. These facts justify the reading
  of the listed premise; they do not supply an omitted guard. For example,
  `n - r < n` supplies the uint64 guard at `n - r` when `r <= n` is held.
  A non-strict bound does not supply a strict guard, and a wrapping subtraction
  is refused even if its mathematical comparison is true.
- Unused premises are allowed; an unguarded `F` takes `using { }`.

**Outside it**, with what to write instead:

- A premise that is not available: prove it first with `have`.
- A guard that needs a fact you did not list: list it. The context is read
  only for the exact range facts establishing a listed comparison's machine
  reading, not to search for other guard premises.
- A guard that needs arithmetic beyond order and equality chaining: prove it
  with `have ... by solve() using { ... };` and list it.

**Failure, checking, and tools:**

An unavailable premise fails naming its position ("premise 2 `x < n` is not an
available exact fact"); an undischarged guard fails with "instantiated premise
... does not follow from the listed evidence". Click performs the named
instantiation; expansion is unchanged, and profiling charges the explicit
premises and result.

**Checked examples:** [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`instantiate_a_universal_over_uint64.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_a_universal_over_uint64.md), [`instantiate_using_names_the_unavailable_premise.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_using_names_the_unavailable_premise.md)

### Theorem application

**Form:** `apply(theorem(args))`

**Core.** Apply a verified global theorem. In a pure theorem proof, its
written `requires` clauses are instantiated as obligations; the proof driver
runs ordinary implicit `solve()` on each one and retains the proofs. You can
also establish the premises first with `have P by { ... }`.

Execution and fixed-state applications still select available premises. Native,
model, and Integer argument evaluation can require explicit domain evidence;
this premise-obligation slice does not replace that evidence-selection route.
Special built-in range-fold and population-count applications retain their
existing rules.

**Failure, checking, and tools:**

An unknown theorem, type mismatch, or unproved premise fails without changing
resources. Pure premise failures name the obligation. Expansion retains ordinary
`have` proofs followed by `apply(...) using { ... }`; the explicit `using` form
continues to require the listed facts and performs no implicit premise solving.

**Checked examples:** [`pure_theorem_apply.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_theorem_apply.md), [`pure_apply_obligations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_apply_obligations.md), [`apply_cites_a_premise_stated_first.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_cites_a_premise_stated_first.md)

### Theorem application with selected premises

**Form:** `apply(theorem(args)) using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which selects its premises; list them only to pin the proof down.
Apply a verified global theorem using exactly the listed premises and add its
guarantees.

**Accepts** an application of a known theorem to arguments of its parameter
types, when:

- Each listed `P` is an available fact, as written, in an equivalent operand
  spelling (`y > x` for `x < y`, `0 == f(x)` for `f(x) == 0`), or as a
  conjunct of a held conjunction.
- Each `requires` of the theorem, with the arguments substituted
  simultaneously, either evaluates to true or matches a listed premise: as
  written, as a conjunct of a listed conjunction (such as the no-overflow
  conjunct of a `defined(x + y)` fact), in the other orientation of an
  equality (`have a == b` discharges `b == a`), or as the mirrored order
  claim in any order family (`c >= b` for `b <= c`). Listing more premises
  than the theorem needs is allowed.
- Mathematical `Integer` arguments may use explicit machine observations such
  as `to_integer(a)`; fixed-state capture checks arithmetic evaluation guards
  and preserves `old`/`at` selectors. Heap observations follow logical
  specification read semantics and grant no access authority.
- Guarantees: every `ensures` of the theorem at the arguments is added. When
  one of them is the current goal, the goal closes unless other written steps
  follow, as for any tactic that adds a fact.

**Outside it**, with what to write instead:

- A requirement that only follows from listed premises, such as `x < y` from
  `x < z` and `z <= y`, or from `x == z` and `z < y`: prove it first with
  `have` and list it.
- An omitted requirement: list it, or use bare `apply`, which selects or
  proves it.

Bare `apply` also selects known evaluation guards for expressions nested inside
model arguments, such as `defined(x - 1)` for `Count::At(x - 1)`. These are
selected argument conditions, not additional theorem requirements; removing
their evidence from an expanded `using` list can make the application fail.

**Failure, checking, and tools:**

An unavailable listed premise fails with "`apply using` requires an
unavailable exact premise"; an unmet requirement fails naming it and its
instantiation ("requirement 1 `a < b` with a = x, b = y instantiates to
x < y"); an unknown theorem or wrong argument count fails naming it. Click
checks the exact application with no search; expansion is unchanged, and
profiling charges its explicit input and guarantees.

**Checked examples:** [`produced_population_count_in_ensured_predicate.md`](https://github.com/clicklang/click/blob/master/mdtests/produced_population_count_in_ensured_predicate.md), [`apply_keeps_sibling_conclusions_when_one_is_the_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_keeps_sibling_conclusions_when_one_is_the_goal.md), [`apply_does_not_supply_a_conclusion_its_theorem_lacks.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_does_not_supply_a_conclusion_its_theorem_lacks.md), [`apply_using_accepts_a_constant_true_premise.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_using_accepts_a_constant_true_premise.md), [`theorem_apply_requires_exact_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_apply_requires_exact_fact.md)

### Unfolding pure functions

**Form:** `unfold(function(args))`

**Core.** Expose one defining equation for the exact pure-function call at the
current proof state and refresh the current goal through that one layer.
Integer arguments resolve in their lexical proof scope, including `intro` and
`obtain` binders; a proof local shadows a same-named theorem parameter.

**Accepts** a call of a known pure function with the declared number of
arguments, each of the parameter's type or exactly convertible to it, whose
names are in scope, and:

- Adds `function(args) == body`, the body with the arguments substituted for
  the parameters and with a `match` on a constructor reduced to its arm. That
  is one layer: calls in the body, including recursive ones and calls of
  other pure functions, stay folded.
- Rewrites every occurrence of that call in the goal, matched as written or,
  failing that, as the same typed kernel term (`unfold(f(2))` rewrites
  `f(1 + 1)`), including occurrences under a binder whose variable the
  arguments do not mention. Calls at other arguments are unchanged, and facts
  are not rewritten; the added equation relates them. A call that does not
  occur leaves the goal unchanged and is not refused.
- Lowers the rewritten goal again, which evaluates constant subterms the
  substitution exposed: a constant `if` condition selects its arm, and width
  conversions of constants fold, so `(uint64)` of an `int32` constant becomes
  a `uint64` constant. Nothing else is normalized.
- Closes the goal when the refreshed goal is an available fact, such as the
  equation just added. After that only `known`, `solve`, or `normalize`
  may follow.
- At a C execution frontier, adds the equation and leaves the frontier.

**Outside it**, with what to write instead:

- A refreshed goal that became `true` or reflexive, such as `x + 1 == x + 1`:
  it stays open; close it with `normalize()`.
- A call whose arguments mention a quantifier's binder before it is
  introduced: `intro()` first.
- More than one layer: `unfold` again at the exposed call.
- A function whose body is a range fold over a symbolic range, or a fold at
  constant endpoints that `normalize` should evaluate: `peel`.
- A `using` list: `unfold` takes none; write `peel(f(args)) using { ... }`.

The refreshed goal can also come out further simplified, as the lowering of
the rewritten goal does: `n + k - k` over `int32` reduced to `n` in one probe.
That is not guaranteed; follow with `normalize()` or `solve() using { ... }` when the
goal needs it.

**Failure, checking, and tools:**

An unknown function ("unknown pure function `h` in `unfold`") or an argument
count mismatch fails; an argument that does not lower at this point fails with
"could not lower defining equation". Expansion is unchanged, and profiling
charges the arguments and one body layer.

**Checked examples:** [`pure_function_unfold.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_function_unfold.md), [`unfold_rewrites_each_occurrence_of_the_exact_call.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_rewrites_each_occurrence_of_the_exact_call.md), [`normalize_evaluates_a_substituted_conversion.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_evaluates_a_substituted_conversion.md), [`a_step_after_an_unfold_that_closed_the_goal_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/a_step_after_an_unfold_that_closed_the_goal_is_refused.md), [`unfold_function_after_integer_intro.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_function_after_integer_intro.md), [`unfold_function_integer_shadow.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_function_integer_shadow.md), [`unfold_using_names_peel.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_using_names_peel.md)

### Peeling a pure function

**Form:** `peel(function(args)) using { P; ... }`

**Specialized.** Write it to open one step of a range-fold function, such as a
sum over an array prefix, in an induction over its end. The single produced
fact is a range-fold law stated over the call itself, and the goal is
refreshed through it, so a range fact about a whole array range is provable by
the existing `induct(hi)`.

**Accepts** an `Integer`-valued pure function whose body is exactly
`(lo..hi).fold(initial, |acc, k| { ... })`, a call of it, and a `using` list
whose every premise is an available fact (as written or in an equivalent
operand spelling). The listed premises select the law, empty first:

- Empty range: listed `hi <= lo` (or `lo >= hi`), at the call's arguments,
  gives `f(args) == initial`.
- Append last cell: listed `lo <= hi - 1` and `hi - 1 < 2147483647` give
  `f(.., hi) == f(.., hi - 1) + <body at acc = f(.., hi - 1), k = hi - 1>`.
  For a `uint64` range the guards are `lo <= hi - 1u64` and
  `hi - 1u64 < 18446744073709551615u64`. This form needs the fold's end to be
  a parameter of the function that its start, initial value, and body do not
  read.
- Constant endpoints: the kernel has already reduced the fold, so the result
  is the defining equation as reduced (over `0..0`, `f(args) == initial`);
  the list is still required and checked for availability but selects
  nothing.
- The goal's occurrences of the call are replaced by the law's right side,
  and the goal closes when the result is an available fact.

**Outside it**, with what to write instead:

- A guard in another form, such as `hi < lo` or `hi == lo` for the empty
  range, or `lo < hi` for the append form: prove the exact guard first with
  `have hi <= lo by solve() using { ... };` and list it.
- A missing `using` list: write one; `unfold` takes no list.
- A fold whose end is an expression such as `n + 1`, or whose body reads the
  end parameter: only the empty-range law applies; restate the function with
  the end as its own parameter.
- An `int32`-valued fold: state the function as `Integer`-valued.
- A refreshed goal that became reflexive, including when the goal was the law
  itself: it stays open; close it with `solve()` or `normalize()`.

`peel` of an `Integer`-valued function whose body is not a fold currently gives
its defining equation, as `unfold` would. That is not guaranteed.

**Failure, checking, and tools:**

The step is a derived use of the two kernel fold laws: the raw defining
equation and its predecessor instance are the law's own premises and stay
inside the step. Every guard must be an exact listed premise; nothing is
searched. A list that selects neither law is refused with what each form still
wants ("The empty-range equation needs `hi <= lo`; the append-last-cell
equation needs `to_integer(hi - 1) < 2147483647`"). A guard over machine `+`,
`-` or `*` is named by its observation, which lowers to the native guard;
the spelling `hi - 1 < 2147483647` is exact Integer arithmetic, a different
proposition. Expansion is unchanged, and profiling charges one law instance.

**Checked examples:** [`unfold_fold_function_empty_range.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_function_empty_range.md), [`unfold_fold_function_appends_last_cell.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_function_appends_last_cell.md), [`fold_function_is_nonnegative_by_induction.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_function_is_nonnegative_by_induction.md), [`unfold_fold_function_requires_a_range_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_function_requires_a_range_guard.md), [`peel_at_a_constant_range_gives_the_defining_equation.md`](https://github.com/clicklang/click/blob/master/mdtests/peel_at_a_constant_range_gives_the_defining_equation.md), [`peel_requires_its_using_list.md`](https://github.com/clicklang/click/blob/master/mdtests/peel_requires_its_using_list.md)

### Constructor matches

**Form:** `match value [ensuring { ... }] { Type::Variant(fields) => { ... } ... }`

**Core.** In a pure proposition proof (including structural-induction arms), or
at any execution frontier the proof has reached — unchanged function entry,
after executed statements, or a loop's `preserve` body — split an ADT of any
width into exhaustive execution proofs, one arm per constructor.

The live arms are joined by a balanced tree of frontier splits, so three or more
constructors need no extra wrapper functions. Fields are fresh typed, arm-local
symbolic values, in scope for the whole arm including the arms of a `branch` or
proof-level `if` written inside it and the body of a `have`; nested entry
matches are supported. An arm that reaches function exit keeps its fields on
that finished path only: the other arm of an enclosing proof `if` starts in the
scope the `if` was written in, and may bind the same names
(`mdtests/each_proof_if_arm_may_reuse_a_match_binding_name.md`,
`mdtests/a_match_binding_does_not_reach_the_other_proof_if_arm.md`).

Where the arms end follows the region: in a function proof with nothing written
after the `match`, each live arm must reach function exit and the arms are
joined there; with tactics written after it, every live arm must end at the same
point in the same state, and the arms rejoin there so those tactics are
checked once, without the constructor facts or fields of any arm; in a loop's
`preserve` body with nothing written after the `match`, each live arm must
execute one complete iteration on its own path — restoring the loop binder,
closing the invariants and satisfying the structural descent at the body's end
or at a `continue`, or leaving through a `break`, which owes none of those.

At function exit, after `step_until(function.exit)`, the `match` is decided
on the one path there, as a proof `if` or `cases` is: when the path's facts
select one constructor only that arm runs, and otherwise the path splits into
one case per live arm. Each live arm finishes its own case
(`mdtests/match_after_execution_finishes_each_arm.md`), and with more than one
live arm, tactics written after the `match` are refused, since they would be
checked once per arm (`mdtests/match_after_execution_that_would_fork_is_refused.md`).
A `match` written inside an arm of an `if` or `cases` at function exit is
decided the same way, with the arm's field bindings
(`mdtests/a_match_in_a_post_execution_if_arm_takes_each_paths_arm.md`,
`mdtests/a_match_in_a_post_execution_cases_arm_takes_each_paths_arm.md`).
Tactics written after it in the same arm are part of that arm, so they
continue each of its cases, as after a nested `if`
(`mdtests/tactics_after_a_nested_post_execution_match_continue_each_path.md`).
A `match` with `ensuring`, or with an arm that is a lone `contradiction`,
splits once at the exit frontier instead, on the path's facts, and so does a
`match` whose scrutinee has no checked value there.

Tactics written after a `match` in a `preserve` body are checked once:
straight-line arms that end in one state rejoin as in a function body, and two
arms still live at one point that end apart are refused
(`mdtests/loop_body_proof_match_shared_continuation.md`). With `ensuring`, arms
that end apart rejoin inside the body, as the arms of a `branch` do, and those
tactics are checked once on the one path that leaves the `match`
(`mdtests/loop_body_proof_match_ensuring_rejoins.md`); a proof `if ... ensuring`
in a `preserve` body rejoins the same way.

The constructor equation is an entry assumption of the whole function only when
the `match` ran before any C step. Pure arms prove the same current goal under
fresh, typed payload bindings and the constructor equation; they add no
induction hypothesis and accept no `ensuring` clause.

Payload names are local to the written arm, including when tactics follow the
match. The kernel reduces the goal to universally quantified constructor
implications and checks their complete conjunction. An impossible arm may
consist of `contradiction(proposition)` naming an exact fact and its negation in
that case; the remaining live arms are split and joined normally, and a sole
live arm runs on the parent frontier without a join.

**Failure, checking, and tools:**

Missing, duplicate, wrong-type/arity, or escaping fields fail. Matching grants
no memory: each live arm must independently unfold and restore its owned
resources. Excluded arms retain checked contradictions, not simulated C
outcomes. Expansion retains and checks every arm. Arms that end in different
states rejoin through `ensuring { fact ...; owns ...; }`, written after the
scrutinee, exactly as the arms of a proof `if ... ensuring` do; a `match` over
more than two constructors is joined pairwise through the same interface.

Without `ensuring`, arms that end in different states are refused. Exclusion
after local proof prefixes and all-impossible matches remain unsupported.

**Checked examples:** [`proof_match_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_resource.md), [`proof_match_three_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_three_constructors.md), [`proof_match_four_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_four_constructors.md), [`proof_match_live_arms_beside_an_excluded_one.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_live_arms_beside_an_excluded_one.md), [`match_bindings_in_branch_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/match_bindings_in_branch_arm.md), [`proof_match_after_c_step.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_after_c_step.md), [`loop_body_proof_match.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_body_proof_match.md), [`loop_body_proof_match_two_live_arms.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_body_proof_match_two_live_arms.md), [`loop_body_proof_match_shared_continuation.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_body_proof_match_shared_continuation.md), [`proof_match_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_arms_rejoin.md), [`proof_match_arms_must_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_arms_must_rejoin.md), [`proof_match_three_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_three_arms_rejoin.md), [`proof_match_ensuring_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_ensuring_rejoins.md), [`proof_match_ensuring_three_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_ensuring_three_constructors.md), [`pure_match_constructor_cases.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_match_constructor_cases.md), [`pure_match_in_induction_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_match_in_induction_arm.md), [`pure_match_typed_payloads.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_match_typed_payloads.md), [`a_pure_match_runs_inside_an_if_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/a_pure_match_runs_inside_an_if_arm.md)

### Scalar induction

**Form:** `induct(n) as ih`

**Core.** As the first step of a pure theorem over an `int32` or `uint64` parameter
`n`, introduce a strong induction hypothesis named `ih`. The signed measure
requires a nonnegative domain; the unsigned measure has that domain intrinsically.

**Accepts** a pure theorem `ensures ... by { ... }` script whose first tactic is
`induct(n) as ih`, when:

- `n` names a theorem parameter of type `int32` or `uint64`. Other parameters
  of any type, including `Integer`, may sit beside it.
- For `int32`, a fact on hand bounds `n` itself below by a constant: `n >= c`
  or `c <= n` with `c >= 0`, or `n > -1`. A requirement stated as a
  conjunction, such as `requires n >= 0 and n <= 10;`, supplies it. A `uint64`
  measure needs no domain fact.

It adds one fact, `ih`: for every `m` of the measure's type, `m >= 0` (signed
only), `m < n`, and every theorem requirement at `m`, together with the extent
halves of each range that requirement names at `m`, imply the theorem's goal
at `m`. Every other parameter keeps its current value. The goal is unchanged.
The script then uses `ih` through `apply(ih(m))` or
`apply(ih(m)) using { ... }`, at its top level and inside nested `if`, `both`,
`cases`, `have`, and `match` blocks.

**Outside it**, with what to write instead:

- `induct` after another tactic, or a second `induct` in the same script: make
  it the first tactic and induct once.
- A parameter of another C width (`uint32`, `int64`, ...), an `Integer`, or an
  algebraic value: induct on an `int32` or `uint64` parameter, or use
  `induct(xs) as ih { ... }` for an algebraic one.
- A signed domain that only follows from other facts, such as `0 <= m` and
  `m <= n`: add `requires n >= 0;` and prove that requirement where the
  theorem is applied.
- `induct` in a C function proof: state the property as a pure theorem and
  apply it.

**Failure, checking, and tools:**

A later position, unsupported parameter type, or unproved signed nonnegative
domain fails with a message naming the case. `induct` in a C function proof
is refused with the generic "no checked proof driver accepts this proof
script's shape". Click opens the
induction rule; expansion is unchanged, and profiling charges the structural
setup.

**Checked examples:** [`pure_induction_countdown.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown.md),
[`an_induction_hypothesis_applies_inside_a_have.md`](https://github.com/clicklang/click/blob/master/mdtests/an_induction_hypothesis_applies_inside_a_have.md),
[`an_induction_hypothesis_applies_inside_match_arms.md`](https://github.com/clicklang/click/blob/master/mdtests/an_induction_hypothesis_applies_inside_match_arms.md),
[`an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.md`](https://github.com/clicklang/click/blob/master/mdtests/an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.md),
[`uint64_measure_induction_counts_a_range_fold.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_measure_induction_counts_a_range_fold.md),
[`pure_induction_keeps_other_parameters_fixed.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_keeps_other_parameters_fixed.md),
[`pure_induction_requires_nonnegative_domain.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_requires_nonnegative_domain.md),
and [`scalar_induction_domain_needs_a_bound_on_the_measure.md`](https://github.com/clicklang/click/blob/master/mdtests/scalar_induction_domain_needs_a_bound_on_the_measure.md).

### Algebraic induction

**Form:** `induct(xs) as ih { Type::Variant(fields) => { ... } ... }`

**Core.** Prove a pure theorem for a recursive algebraic parameter by exhaustive
constructor cases; each immediate recursive field admits `ih(field)`, and
`ih(field, other, ...)` states the theorem at that field and any well-typed
terms in the remaining parameter positions.

**Failure, checking, and tools:**

A missing, duplicate, unknown, or wrong-arity arm fails. Bindings are arm-local,
and `ih` rejects nonrecursive or non-immediate values in the inducted position,
a parameter list of the wrong length, and an instantiation whose substituted
requirements are unavailable. Click checks every arm; expansion recurses through
the arm certificates.

**Checked examples:** [`algebraic_structural_induction.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_structural_induction.md), [`algebraic_structural_induction_generalizes_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_structural_induction_generalizes_parameters.md)

### Induction hypothesis application

**Form:** `apply(ih(m))`

**Core.** Select the available facts `m < n` and the theorem requirements at
`m`, and `0 <= m` for a signed measure, then instantiate the local induction
hypothesis. None is proved: state a missing one first with `have`. Under a
structural `induct` the obligations are instead the theorem's requirements at
the spelled parameter list, and the descent is the inducted argument naming a
field of the current arm.

**Failure, checking, and tools:**

A bounded selection miss, nondecreasing argument, or violated requirement
fails. A premise that is not an available fact is a search miss: the refusal
says so and names the `have` that states the premise. Click checks the
selected operations; expansion adds a `using` block.

**Checked examples:** [`pure_induction_countdown.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown.md)

### Induction hypotheses with selected premises

**Form:** `apply(ih(m)) using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which selects the decrease and requirements. Instantiate the local induction
hypothesis from exactly the listed strict-decrease and substituted-requirement
obligations, including nonnegativity for a signed measure.

**Accepts**, after scalar `induct(n) as ih`, one argument `m` of the measure's
type (any expression, such as `n - 1` or `n - 1u64`), when:

- Every listed `P` is an available fact, read as `using` lists read premises:
  exactly, under another spelling of the same order claim (`0 <= m` for
  `m >= 0`, `n > m` for `m < n`), or true without facts. Listing a range a
  clause stated also cites its two extent halves where they are available.
  Extra or repeated premises are allowed.
- Every guard of the hypothesis at `m`, split into its `and` conjuncts, is
  true by context-free evaluation or is one listed premise under one of those
  spellings. The guards are `m >= 0` (signed only), `m < n`, each requirement
  at `m`, and the extent halves of every range a requirement names at `m`.

It adds the theorem's goal at `m` as a fact and closes the current goal when
that fact is the goal. Nothing else in context is read.

**Outside it**, with what to write instead:

- A guard that is not listed, including one held as a fact: add it to the list;
  prove it first with `have` when it is not yet a fact.
- A listed conjunction `A and B` that is not itself a fact: list `A` and `B`
  separately.
- More than one argument: measure induction takes the measure alone and holds
  the other parameters fixed.
- An argument of another type than the measure, such as `1u64` for an `int32`
  `n`: convert it.

A guard may also close by the kernel's order reasoning over several listed
premises, so `n - 1 < n` and `n <= 100` together discharge `n - 1 <= 100`.
That is not a documented guarantee; list the instantiated guard itself.

**Failure, checking, and tools:**

A missing guard prints it at `m` (``instantiated premise `n - 1 >= 0` does not
follow from the listed evidence``); an unavailable listed premise prints that
premise with the theorem's parameter names (``induction premise is not exactly
available: n - 2 < n``). Click performs one local instantiation with no premise
search; expansion is unchanged.

**Checked examples:** [`pure_induction_countdown_explicit.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown_explicit.md),
[`induction_hypothesis_cites_a_listed_range_with_its_extent.md`](https://github.com/clicklang/click/blob/master/mdtests/induction_hypothesis_cites_a_listed_range_with_its_extent.md),
and [`induction_hypothesis_owes_the_range_extent.md`](https://github.com/clicklang/click/blob/master/mdtests/induction_hypothesis_owes_the_range_extent.md).

### Intermediate facts

**Form:** `have P by { ... }`

**Core.** Open a nested goal `P`; on success, add `P` to the surrounding context
without changing its execution frontier. `have P;` without a proof is `have P by
solve();`, and a one-step proof may drop the braces: `have P by T(args);`. A
`have` executes no C. On a linear `Integer` bound `solve`
refutes the integer negation from the facts connected to `P` and applies the
result as one `arithmetic_certificate`
([`have_by_solve_refutes_a_linear_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/have_by_solve_refutes_a_linear_bound.md)).

Connected `int32`, `int64` and `uint64` order facts are carried to `Integer` by
`known()`, since a comparison of observations is the native comparison,
and `uint64` values get their type range from a `type_range` certificate; only
the carried facts the certificate cites are kept
([`solve_carries_machine_orders_to_integer.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_carries_machine_orders_to_integer.md)).

A `uint64` or `int64` order goal, or an `int32` `<=` goal, is proved through its
`Integer` reading, which is the native comparison itself
([`solve_proves_a_machine_order_through_integer.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_a_machine_order_through_integer.md)),
and an `Integer` equality goal from both of its bounds
([`solve_proves_an_integer_equality_from_both_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_an_integer_equality_from_both_bounds.md)).

A goal `defined(a + b)` or `defined(a - b)` over `int32` or `int64` is proved
from both `Integer` bounds of the exact result, which together are the
definedness fact
([`solve_proves_signed_addition_defined.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_signed_addition_defined.md)),
and each `to_integer(a + b)` or `to_integer(a - b)` in the goal is observed term
by term: a signed operation once it is defined, and a `uint64` one once it
does not wrap, by an `integer_operation_identity` certificate citing both
constant bounds of its exact value
([`solve_observes_an_operation_term_by_term.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_observes_an_operation_term_by_term.md)).

Machine equality facts are carried by rewriting, each observed value gets its
type range from a `type_range` certificate, an `int32`, `int64` or `uint64`
equality goal is
proved as its observed reading once both sides are shown defined, splitting an
equality into its two bounds when needed, and a conjunction goal is split
([`solve_proves_a_conservation_equation.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_a_conservation_equation.md)).
On an implication `A implies B`, `solve` introduces `A` and closes `B`, with
this arithmetic and the searches below, as for `result == 1 implies cap ==
old(cap) + 1` on a path where the antecedent reads `true`
([`solve_proves_an_implication_whose_consequent_needs_the_solver.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_an_implication_whose_consequent_needs_the_solver.md)).
The in-range `+`, `-` and `*` identities, a product's bounds from its
operands' type ranges by `integer_product_bounds` included
([`solve_observes_a_product_by_a_constant.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_observes_a_product_by_a_constant.md),
[`a_product_of_64_bit_values_is_its_exact_product.md`](https://github.com/clicklang/click/blob/master/mdtests/a_product_of_64_bit_values_is_its_exact_product.md)),
and integral-cast identities this arithmetic uses, nested ones included, are
described in [mathematical integers](../../internals/mathematical-integers.md#in-range-machine-sums-differences-and-products).

When its other strategies miss, `solve` searches chains of at most three
`rewrite` steps by the equalities connected to `P`, machine, `Integer` and
algebraic alike, each in either direction, and closes the rewritten goal by
`known`, the direct logical closer or, a few times per search,
`solve`.

Each rewrite is a checked step, and the search offers at most 64 equalities,
those that rewrite `P` itself first, and tries at most 256 rewrites, so a large
connected component fails promptly
([`solve_rewrites_a_constructor_term_to_its_model.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_rewrites_a_constructor_term_to_its_model.md),
[`solve_refuses_a_constructor_rewrite_that_does_not_close.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_refuses_a_constructor_rewrite_that_does_not_close.md)).

The search cites only equalities with a source spelling at that point; a fact
from an earlier `have` or a proof `if` condition inside a pure theorem has none
and is not offered. In a pure theorem, an omitted proof of `ensures P` is the
same `solve`. `have name: P` also names the fact: until the end of
the enclosing block, `name` stands for `P` wherever a proposition is cited
whole, as in `using { name; }`, `extract(name)` or `contradiction(name)`, and is
read as `P` there, so citing it proves exactly what restating `P` proves.

The name is not visible inside the fact's own proof, and expansion writes `P` in
full
([`have_names_a_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/have_names_a_fact.md)).

**Failure, checking, and tools:**

Any unfinished nested goal fails and adds nothing. A fact name that is already a
parameter, binding or fact name in scope is refused
([`have_name_refuses_a_name_in_scope.md`](https://github.com/clicklang/click/blob/master/mdtests/have_name_refuses_a_name_in_scope.md)).
Citing a name inside its fact's own proof or after its block ends is refused
with that reason
([`have_name_is_not_cited_in_its_own_proof.md`](https://github.com/clicklang/click/blob/master/mdtests/have_name_is_not_cited_in_its_own_proof.md),
[`have_name_is_cited_only_in_its_block.md`](https://github.com/clicklang/click/blob/master/mdtests/have_name_is_cited_only_in_its_block.md)).

A quantifier variable hides a fact of the same name in its body, and `intro() as
name` refuses a fact name in scope.
The container stays intrinsically control; its selectable source site may own
simple work or expandable automation from its body.

**Checked examples:** [`post_execution_have_checks_each_path.md`](https://github.com/clicklang/click/blob/master/mdtests/post_execution_have_checks_each_path.md), [`have_names_a_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/have_names_a_fact.md)

### Proposition branches

**Form:** `if P [ensuring { ... } then] { ... } else { ... }`

**Core.** Split pure reasoning into contexts containing `P` and `not P`, then
require both to prove the same goal. At an execution frontier, straight-line
arms that end at the same point in the same state rejoin: the proof
continues once from that state, with the facts both arms established.

The arms may reason, run the same C statements, and unfold and refold resources.
The case facts and anything only one arm proved do not survive the join. With
`ensuring { fact ...; owns ...; views ...; } then`, the arms must rejoin through
that interface, as the arms of a `branch ensuring` do: both arms establish every
interface fact and hold every interface resource, and the proof continues once
from the state the interface describes, even when the arms ended in different
states.

`owns name: resource(...);` names an instance that carries fields: each arm
supplies the instance it has bound to `name`, the join gives `name` a fresh
model, and the interface's `fact` entries, checked against each arm's own model,
are all the proof knows about the fresh one. What follows the `if` is checked
once.

Without `ensuring`, two arms that are both still live and end in different
states or at different points are refused when tactics follow the `if`
(`mdtests/proof_if_arms_must_rejoin.md`); when one arm reaches function exit,
those tactics belong to the other arm and run once, in it
(`mdtests/proof_if_one_arm_returns_and_the_other_continues.md`).

In a loop's `preserve` body the rule is the same, except that arms reaching
those tactics at different points are different paths of the C and each
is finished its own way.

At function exit the C state is fixed. When the path's facts already decide
`P`, only the matching arm runs. When `P` is open and tactics follow the `if`,
the `if` is refused, because its arms would not rejoin and what follows would
be checked once per arm (`mdtests/a_proof_if_after_execution_that_would_fork_is_refused.md`).
Write those tactics inside the arms instead
(`mdtests/a_proof_if_after_execution_closes_its_claims_in_each_arm.md`).

**Failure, checking, and tools:**

Either unfinished arm fails. Click checks both spelled branches; expansion
recurses into smart descendants, and profiling reports them.

**Checked examples:** [`proof_if_cases.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_cases.md), [`proof_if_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_arms_rejoin.md), [`proof_if_arms_rejoin_after_c_steps.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_arms_rejoin_after_c_steps.md), [`proof_if_ensuring_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_rejoins.md), [`proof_if_ensuring_named_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_named_resource.md), [`proof_if_ensuring_named_resource_needs_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_named_resource_needs_fact.md)

### Explicit cases

**Form:** `cases { A => { ... } B => { ... } }`

**Specialized.** Write it to use a disjunction that is already a fact, when its
arms are not `P` and `not P`; otherwise use `if`. Eliminate an exact available
disjunction: each arm receives exactly its own disjunct. Use `if P` to split on
a proposition you choose, which needs no premise because `P or not P` always
holds.

There is one arm per disjunct, any number from two, and the disjunction of the
arms grouped left to right as `or` parses (`A or B or C` is `(A or B) or C`)
must be available. Proving a focused proposition, every arm proves it. At an
execution frontier `cases` is a case split like a proof `if`, and follows the
same rule: with tactics written after it, its arms rejoin with the facts every
arm proved, or the `cases` is refused
(`mdtests/cases_arms_rejoin_with_the_facts_every_arm_proved.md`,
`mdtests/cases_arms_that_do_not_rejoin_are_refused.md`); an arm that reaches
function exit finishes its own path
(`mdtests/cases_at_a_frontier_finishes_each_arm.md`). In a loop's `preserve`
proof its arms must rejoin: each arm closes its own back edge, and the
rejoined path's back edge is then closed again with only the facts every arm
proved, so an arm that needs its own fact there proves the invariants at the
next iteration, the same proposition in every arm
(`mdtests/a_preserve_cases_rejoin_keeps_only_the_facts_every_arm_proved.md`,
`mdtests/a_preserve_cases_arm_keeps_a_fact_every_arm_proves.md`). At function exit it splits the path there as a
proof `if` does: when the path's facts decide a disjunct only that arm runs;
otherwise the path splits into one case per arm, which needs the disjunction as
an exact fact on the path (`mdtests/cases_after_execution_splits_each_outcome_path.md`,
`mdtests/cases_after_execution_takes_the_decided_arm.md`), and tactics written
after a `cases` that forks are refused
(`mdtests/cases_after_execution_that_would_fork_is_refused.md`).

**Failure, checking, and tools:**

An unavailable disjunction or unfinished arm fails; this never substitutes `not
A` for `B` or implicitly branches C. Click checks both proof branches, expansion
recurses, and profiling reports descendants.

**Checked examples:** [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`cases_in_have_before_and_after_execute.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_in_have_before_and_after_execute.md), [`cases_at_a_frontier_finishes_each_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_at_a_frontier_finishes_each_arm.md), [`cases_arms_rejoin_with_the_facts_every_arm_proved.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_arms_rejoin_with_the_facts_every_arm_proved.md), [`cases_at_a_frontier_requires_its_disjunction.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_at_a_frontier_requires_its_disjunction.md), [`cases_after_execution_splits_each_outcome_path.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_after_execution_splits_each_outcome_path.md), [`cases_after_execution_requires_its_disjunction.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_after_execution_requires_its_disjunction.md)

### Scoped resource opening

**Form:** `open(resource) { ... }`

**Specialized.** Write it to work inside one layer of a composite resource and
have it folded back automatically at the end of the block. Temporarily replace a
held composite resource with one body layer, check the nested proof, then fold
it at scope exit. A model `match` inside the block uses the ordinary checked
constructor arms and joins: terminal arms each restore the resource at return;
an `ensuring` interface can rejoin before the block closes.

**Failure, checking, and tools:**

Missing ownership, an undecided guard, or failure to restore the body fails. A
body fact the closing fold leaves open is proved by the implicit closer, which
expansion prints as `open(...) { ... } by { ... }`. Click checks the exact
resource transition; expansion recurses, and profiling reports descendants.

**Checked examples:** [`resource_population_open.md`](https://github.com/clicklang/click/blob/master/mdtests/resource_population_open.md), [`open_scope_model_match_terminal.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_terminal.md), [`open_scope_model_match_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_rejoins.md), [`open_scope_model_match_rejects_bad_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_rejects_bad_arm.md)

### Scoped resource opening with restoration

**Form:** `open(...) { ... } by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
the close a different proof than the implicit closer. Closing an `open` scope
folds its resource again; the body after `by` proves the one body fact that fold
leaves open, as `fold(...) by { ... }` does, where the block ends, or after
execution when the block reaches function exit.

A bare `open` proves that fact by the implicit closer, which expansion prints as
this `by`. The body is one tactic call, such as `solve();`, or a block.

**Failure, checking, and tools:**

Refused when the close leaves no body fact open (superfluous) or more than one;
prove the others with `have` in the block. Expansion keeps the `by` and
prints the body's checked steps; a smart tactic written in the `by` expands with its claim
(`click expand --claim`), not as a site of its own.

**Checked examples:** [`open_by_proves_the_closing_fold_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/open_by_proves_the_closing_fold_body_fact.md), [`open_by_is_refused_when_the_close_leaves_nothing_open.md`](https://github.com/clicklang/click/blob/master/mdtests/open_by_is_refused_when_the_close_leaves_nothing_open.md)

### Existential witnesses

**Form:** `witness { name: value, ... };`

**Specialized.** Write it for an existential goal, naming the value that
satisfies it. On an existential goal, instantiate each named binder with its
value, in the order written, and continue with the instantiated body. One
`witness` can supply every binder of `exists (x: T, y: U) { ... }`.

**Accepts** a goal whose outermost form is `exists (name: T) { B }` or
`(lo..hi).any(|name| { B })`, in a pure theorem or a C proof, when:

- Each written name is the goal's outermost binder at that point:
  `witness { x: 3, y: 4 }` on `exists (x: int32, y: int32) { ... }` takes `x`,
  then `y`. Several `witness` steps may supply the binders one at a time.
- Each value has its binder's type: a C integer of exactly that type (`3u64`
  for `uint64`), a pointer, an `Integer` expression such as `0` or
  `to_integer(n)` for `Integer`, or an algebraic value of that datatype.

The goal becomes `B` with the value substituted; for `.any` it becomes
`lo <= value and value < hi` and `B`. No fact is added and the body is not
checked; prove it next.

**Outside it**, with what to write instead:

- An existential below the top of the goal, such as `A and exists ...`: split
  it with `both` first.
- Binders named out of their declared order: name them in order.
- A value of another type, such as an `int32` variable for a `uint64` or
  `Integer` binder: convert it (`to_integer(n)`) or write the suffixed literal.

**Failure, checking, and tools:**

A wrong binder, ill-typed value, or nonexistential goal fails. On a
nonexistential pure goal the message reads "pure `witness` currently requires
an Integer existential proposition" even though C integer and algebraic
binders are accepted. Click records the exact witness; expansion is unchanged,
and profiling charges one instantiation.

**Checked examples:** [`witness_and_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_and_choose.md), [`integer_exists_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_exists_choose.md), [`witness_names_binders_in_their_order.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_names_binders_in_their_order.md)

### Obtaining witnesses

**Form:** `obtain (name: Type, ...) { P }`

**Specialized.** Write it to use an existential fact by naming its witness. Open
an already established `exists (name: Type, ...) { P }`, introducing the bound
values and instantiated body into the proof context. Each name is in scope for
every later tactic of the same proof block, whatever its type: a `have` goal, an
`instantiate` argument or `using` premise, a `contradiction` fact, a theorem
argument, or a `witness`.

**Accepts** an `obtain` whose written `exists (name: Type, ...) { P }` is an
available fact up to the binders' names, held alone or as a leaf conjunct of a
fact (`requires n > 0 and exists (k: int32) { k < n };`), when:

- The fact is a requirement, a `have` conclusion, or another opened body, and
  `P` is spelled as the fact states it, with each binder type the same.
- Binder types are C integers, pointers, `Integer`, or algebraic types.
- Fewer names than the fact's binders open the outer ones, when `P` is written
  as the remaining existential: `obtain (a: int32) { exists (y: int32) { a < y } }`
  opens `exists (x: int32, y: int32) { x < y }` one binder at a time.
- A `(0..n).any(|k| { B })` fact opens with its bounds spelled in the body:
  `obtain (m: int32) { 0 <= m and m < n and B' }`, `B'` being `B` at `m`.
- No name is a parameter, `result`, a local, or an earlier `obtain` name.

Each name is bound to a fresh value, and the body at those values becomes a
fact.

**Outside it**, with what to write instead:

- An existential held only under a disjunction or implication: `cases` or
  `extract` it first.
- A body spelled differently from the fact (`n > m` for `m < n`), or a
  different binder type: write it as the fact states it.
- More names than the fact's binders: name only those it has.

**Failure, checking, and tools:**

An unavailable existential, wrong binder type, or name already in scope fails;
the first two print the written existential as an unsatisfied requirement.
Prove the existential with `have` first if needed. Expansion retains this exact
step.

**Checked examples:** [`integer_exists_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_exists_choose.md), [`witness_and_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_and_choose.md), [`obtain_requires_the_written_existential_body.md`](https://github.com/clicklang/click/blob/master/mdtests/obtain_requires_the_written_existential_body.md)

## Exact integer product bounds

Inside `arithmetic_certificate rules`, the node
`integer_product_bounds bounds [i, j, k, l] => x * y <= T;` checks one
mathematical product bound. Its four references must name exactly available
premises `L <= x`, `x <= U`, `M <= y`, and `y <= N`, in that order. Each
endpoint and the result bound `T` must be a constant Integer, and each
interval must have its lower endpoint at most its upper endpoint.

The checker computes `L*M`, `L*N`, `U*M`, and `U*N` using exact integers.
For an upper bound, all four must be at most `T`; for the result `T <= x * y`,
all four must be at least `T`. The rule accepts negative, zero, and crossing
intervals and bounds weaker than the exact endpoints. It selects four facts
by index and does no premise search or implicit machine-range inference.

The result must contain an Integer multiplication at its root. Products
already reduced to a constant or a single operand, such as `x * 0` or `x * 1`,
use ordinary simplification instead. To relate machine values, multiply
separate observers, such as `to_integer(a) * to_integer(b)`. A bound on that
product does not establish the definedness of the machine operation `a * b`.
Native wide machine arithmetic needs its own checked width and conversion
rules. The [checked regression](https://github.com/clicklang/click/blob/master/mdtests/integer_product_bounds.md)
proves both signed 128-bit range endpoints for a signed 64-by-32-bit
mathematical product.

## Resources and transport

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `transport(P, Q)` | smart | Specialized | Carry a fact from an earlier memory state. | [Reference](#fact-transport) |
| `transport(P, Q) using { R; ... }` | simple | Expansion output | Carry a fact using explicit frame evidence. | [Reference](#transport-with-selected-premises) |
| `unfold(name)` | simple | Core | Make a predicate transparent in the current proof branch. | [Reference](#unfolding-predicates) |
| `unfold(resource(args))` | simple | Core | Open an owned resource instance. | [Reference](#unfolding-resources) |
| `fold(resource)` | simple | Core | Assemble a resource from its body and children. | [Reference](#folding-resources) |
| `fold(...) by { ... }` | control | Expansion output | Supply a proof for one fold obligation. | [Reference](#folding-with-one-obligation) |
| `fold(...) { requires P by ...; }` | control | Expansion output | Supply proofs for selected fold obligations. | [Reference](#folding-with-several-obligations) |
| `construct(resource)` | simple | Specialized | Create an abstract token authorized by a `constructs` clause. | [Reference](#constructing-resources) |
| `take(base[a..b])` | simple | Specialized | Take one element out of iterated ownership. | [Reference](#taking-a-range) |
| `give(base[a..b])` | simple | Specialized | Return a taken element to iterated ownership. | [Reference](#giving-a-range) |
| `gather(resource(args))` | simple | Specialized | Form iterated ownership from its covering range. | [Reference](#gathering-resources) |
| `scatter(resource(args))` | simple | Specialized | Dissolve iterated ownership into its covering range. | [Reference](#scattering-resources) |
| `name(args, { binder: instance })` | simple | Specialized | Apply a verified tactic with resource bindings. | [Reference](#user-defined-tactic-calls) |
| `observe(resource)` | simple | Specialized | Read a resource's persistent observations. | [Reference](#observing-resources) |

Predicate calls are opaque to framing until their definitions are unfolded.
To carry such a fact across C execution, run `unfold(name)` before the relevant
steps and transport the unfolded definition.

### Fact transport

**Form:** `transport(P, Q)`

**Specialized.** Write it when a fact stated at an earlier state is needed at
the current one and neither `step` nor `solve` carried it. When exact source `P`
is available, derive target `Q` at another certified point, citing `P` alone
as frame evidence. No other available fact is searched for: a frame that needs
more premises is written in the `using` form below.

**Failure, checking, and tools:**

Unrelated propositions, unsafe writes, or a source that does not carry the
target alone fail. The refusal is the one the same transport gets with its
source listed in `using`: it names the effects
between the two states and, for a quantified fact, the leaf the frame could
not carry. It ends by calling the miss a search miss: if the target holds,
list the facts that carry the source in the `using` form. Click checks the
chosen transport; expansion adds `using`, and profiling reports search and
leaves.

**Checked examples:** [`simple_statement_step_explicit_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_explicit_transport.md), [`transport_model_pointer_binding.md`](https://github.com/clicklang/click/blob/master/mdtests/transport_model_pointer_binding.md)

### Transport with selected premises

**Form:** `transport(P, Q) using { R; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form
when the source alone carries the target, and list more premises here when it
does not. Derive target proposition `Q` from exact
source `P` using only the listed point and frame evidence. Available in a
pure theorem too, where the listed premises are all there is to read.

**Accepts**, in a C proof or a pure theorem, when:

- Every listed `R` is an available fact, read as every `using` list reads
  premises: exactly, under another spelling of the same order claim, or true
  without facts. A quantified premise may name its own binder: a call's
  postcondition held under the binder its lowering chose is cited by a written
  form with another, as in `apply using`. Listing a stated range also cites
  its two extent halves.
- The source `P` is a listed premise, follows from the listed premises by the
  kernel's atomic derivation (`old(p[0]) <= 7` from `old(p[0]) == 7`), or is
  a reflexive equality, under binders and guards, which needs no entry. At a
  completed return outcome `P` may instead be any held fact, up to its
  binder's name.
- The target `Q` is already available, or the frame carries `P` to it as
  described below. In a pure theorem, which has no state, `Q` must follow from
  `P` and the listed premises alone: `a == 1` with `a == b` listed reaches
  `b == 1`, and `A and B` reaches `A`.

It adds `Q` as a fact and closes the goal when `Q` is the goal.

For current-point `viewable(A)` to `viewable(B)` with explicitly cited
`contains(A, B)`, expansion retains ordinary
`apply(separation::viewable_restrict(A, B)) using { ... }` steps. When both
are memory ranges with the same written base and int32 endpoints, citing
`lo <= inner_lo`, `inner_lo <= inner_hi`, and `inner_hi <= hi` instead
produces an explicit `have contains(...)` using `separation::contains_subrange` first.
These cases expand to ordinary library applications.
See `mdtests/viewable_restrict_transport_expansion.md`.

At an execution frontier, a focused equality between a read now and the same
read at a named statement's entry also expands to `preserve(separate(statement(...).footprint, R))`
when that footprint separation is cited, the source is the earlier read's
reflexive equality, and the statement's recorded exit is the current point.
This covers memory reads and abstract resource fields. The explicit footprint
separation proof remains in the expanded script; no history search is needed
for replay. See `mdtests/single_write_transport_expansion.md` and
`mdtests/single_write_resource_transport_expansion.md`.

For several statements, cite each footprint separation in `using`. Expansion
writes one `have at(statement(i).exit, read) == at(statement(i).entry, read)`
proved by `preserve` per cited footprint, then `known()` joins the
endpoint equalities. The premises can be written in either order; they must
cover the read's path to the current point. No intermediate footprint or
separation is discovered from history, and failure of ordinary equality closure is final rather
than retrying a history search. Both memory reads and abstract resource fields
use this form. See `mdtests/multi_write_transport_expansion.md` and
`mdtests/multi_write_resource_transport_expansion.md`.

A focused comparison with one read operand changing from a statement entry
to the current point uses the same preservation chain. For example,
`transport(at(statement(0).entry, *q) > 0, *q > 0) using { ... }`
first retains the earlier inequality with `known()`, proves the read
equality from the cited footprint separations, then uses `rewrite` and
`known()` to close the current comparison. This also carries a known
value, such as `at(statement(0).entry, *q) == 7` to `*q == 7`. It covers
non-reflexive `==`, `<`, `<=`, `>`, `>=`, and `!=`, with the changing operand
on either side; the other operand and comparison operator must be unchanged. It also applies to abstract
resource fields. The source must already be provable, and all supplied
separations are checked. See `mdtests/inequality_transport_expansion.md` and
`mdtests/known_value_transport_expansion.md`.

The `at(...)` may also wrap the whole source comparison, as in
`transport(at(statement(0).entry, *q == 7), *q == 7) using { ... }`.
The driver uses the same explicit preservation and rewrite steps. Unsuffixed
integer literals are point-independent; every other operand retains an
explicit `at(...)`. Thus an old comparison of two reads can carry one read
while the target explicitly keeps the other at its old point, but this route
does not silently substitute the other's current value. The original source
fact remains in the proof and is checked by `known()`.
See `mdtests/snapshot_comparison_transport_expansion.md`.

When both operands are reads at earlier points, the comparison route can
preserve both: `transport(at(statement(0).entry, *q == *r), *q == *r)`.
Cite the footprint separation for each read in `using`. Expansion writes one
preservation chain per operand, rewrites both, and closes with `known()`.
Selection uses the explicitly written single-cell dereference or named
resource-field subject; it does not discover aliases or prove range containment.
Every supplied separation must be used and checked. See
`mdtests/two_read_transport_expansion.md`.
Conjunction trees of supported scalar comparisons also expand: for example,
`transport(at(statement(0).entry, *q == 7 and (*r == 8 and *s == 9)), *q == 7 and (*r == 8 and *s == 9))`.
Expansion emits nested ordinary `both` proofs, preserving the written grouping,
with a preservation/rewrite proof for each scalar leaf. This form handles
matching conjunction structure; selection and regrouping are described below. The source can wrap the whole tree, a
subtree, or individual leaves in `at(...)`; nested `at(...)` wrappers are not
handled by this route. Each leaf checks its earlier fact with `known()`
and uses the supplied footprint separations for its changing reads. This covers
memory and root fields of named resources across one or several statements.
The explicit separations are indexed once by their written cell or resource,
and every supplied separation must be used and checked. No aliases or range
containment facts are discovered. See `mdtests/conjunction_transport_expansion.md`
and `mdtests/nested_conjunction_transport_expansion.md`.

A historical conjunction can also transport selected scalar comparison leaves:
`transport(at(statement(0).entry, *p == 8 and *q == 7), *q == 7)` keeps one,
while `transport(at(statement(0).entry, *q == 7 and (*p == 8 and *r == 8)), *r == 8 and *q == 7)`
keeps two in a different order. The target may regroup or repeat selected
leaves in a conjunction tree.
The driver indexes the written source's `at(...)` comparison leaves once and
selects each target leaf by exact spelling. It emits a `have` for each selected
historical leaf using `known()`, followed by its ordinary preservation/rewrite
proof, and combines the results with `both` in the target's written shape.
Discarded conjuncts need not remain true; only the selected reads need footprint
separations. The supplied separations are indexed once and must all be used and
checked. Whole-tree and subtree `at(...)` wrappers are supported. An exact
leaf spelling selects one point; this route does not retry other points
or discover additional evidence. Non-comparison leaves and operand-level
`at(...)` spellings remain outside this selection route.
See `mdtests/conjunction_projection_transport_expansion.md` and
`mdtests/conjunction_selection_transport_expansion.md`.

Implications also expand when source and target have matching logical structure
built from `and`, `or`, `not`, nested `implies`, and supported scalar comparison
leaves. For example,
`transport(at(statement(0).entry, (*q == 7 and *r > 0) implies (*q > 0 implies *r == 8)), (*q == 7 and *r > 0) implies (*q > 0 implies *r == 8))`
uses footprint separations for reads throughout the guard and conclusion.
Expansion retains the earlier whole fact with `known()`, proves each
selected read's preservation, then closes the whole goal with `known()`
using those equalities. It emits no whole-goal rewrites and does not assume
that any guard is true. Exact shared read pairs use one preservation chain.
The driver traverses the written logical trees once and indexes explicit
separations by written subject. It does not search for aliases or discover
additional premises. Source `at(...)` forms may wrap the whole implication or
individual subtrees/comparisons; repeated `at(...)` wrappers are unsupported.
Memory reads, named resource fields, two-read comparisons and multiple cited
statements use the same form. Quantifiers and non-comparison leaves remain
outside this route, as do logical regrouping and top-level disjunction transport.
See `mdtests/implication_transport_expansion.md` and
`mdtests/compound_implication_transport_expansion.md`.

Other transport routes still retain their existing form.

The frame carries a fact across the steps between its point and the
target's when every cell it reads is unchanged. The structural frame does so
read by read, including 64-bit equality, preserving the read kind, all eight
bytes, and the other operand; it carries `defined(...)` leaves through the
typed-read transport rule, preserving initialization and lifetime evidence.
Equal read values alone do not justify carrying definedness across
deallocation. See the
[checked disjoint-store regression](https://github.com/clicklang/click/blob/master/mdtests/guarded_definedness_survives_a_disjoint_store.md).
Beyond it:

- A `viewable` target is decided by the kernel's viewability rules, so a range
  narrows to a sub-range the listed order facts place inside it, provided the
  source range is established to be a valid 32-bit byte extent.
- A fact about an application of an `Integer` range-fold function whose body
  the kernel checks, reading its one `T[]` argument (for a C integer `T` such
  as `int32` or `uint64`) only at the fold's own index, crosses each store and
  checked call write set that an exact order fact or stated `separate(...)`
  places outside the application's `lo..hi` cells; the proved application
  equality grants no C access.
- A universal fact `forall (k: int32) { G implies F }` crosses the same steps:
  `k` is renamed fresh, `G` is assumed, and each read of `F` and `G` is carried
  when the recorded history shows its cell unchanged between its two
  points, read against the current context's own facts (for example
  `k < n` excluding a store to `dst[n]`, `k != cur` excluding a store to
  `visited[cur]`, or `0 <= k and k < n` with a contract separation placing
  `left[k]` apart from it).
- A source `A and B` reaches a target that is only `A` or only `B`: after
  `memset(dst, 7, 4); dst[4] = 0;`, `memset`'s guarded postcondition carries
  to `(0u64..4u64).all(|k| { dst[k] == 7 })`.

The rule answers the same for every caller, so `solve`'s transport between points
reaches it too, and `solve` offers an `A and B` source when the goal is held at
a recorded point only as one of its conjuncts.

**Outside it**, with what to write instead:

- A mid-execution source that is an available fact but not listed: list it;
  the refusal names it as one to list.
- A target whose cell a step between the two points may write, such as
  `old(p[0]) == 7` to `p[0] == 7` after `p[0] = 9`: no frame exists; prove the
  target from the step's own facts.
- A pure target that needs a fact not listed, such as `a == 1` to `b == 1`
  without `a == b`: list it.
- Choosing frame evidence: use the bare `transport(P, Q)`.

**Failure, checking, and tools:**

An absent premise prints it as the required transport premise. An absent
source, mismatched target, or insufficient evidence fails. A refused narrowing
names the order fact it needs, as the two segments were written. A refused
frame prints the source and target, as written and as checked, and the cell
walks it performed; a refused fold frame names the step it could not place,
or why the function has no checked read summary; a refused quantified frame
prints the leaf it had and the leaf it wanted. A pure-theorem refusal spells
its propositions with the theorem's parameter names and the names the script
introduced.

Click checks that transport only; expansion is unchanged, and profiling charges
the named evidence.

**Checked examples:** [`field_derived_precise_effect_after_metadata_write.md`](https://github.com/clicklang/click/blob/master/mdtests/field_derived_precise_effect_after_metadata_write.md), [`have_viewable_prefix_of_a_range.md`](https://github.com/clicklang/click/blob/master/mdtests/have_viewable_prefix_of_a_range.md), [`sweep_maintains_a_zero_unmarked_count.md`](https://github.com/clicklang/click/blob/master/mdtests/sweep_maintains_a_zero_unmarked_count.md), [`sweep_prefix_survives_its_endpoint_store_by_solve.md`](https://github.com/clicklang/click/blob/master/mdtests/sweep_prefix_survives_its_endpoint_store_by_solve.md), [`quantified_frame_carries_a_fact_past_the_excluded_store.md`](https://github.com/clicklang/click/blob/master/mdtests/quantified_frame_carries_a_fact_past_the_excluded_store.md), [`quantified_frame_preserves_uint64_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/quantified_frame_preserves_uint64_equality.md), [`memcpy_then_terminator_keeps_copied_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_then_terminator_keeps_copied_bytes.md), [`a_guarded_memset_value_claim_crosses_a_disjoint_store.md`](https://github.com/clicklang/click/blob/master/mdtests/a_guarded_memset_value_claim_crosses_a_disjoint_store.md), [`simple_statement_step_explicit_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_explicit_transport.md)

### Unfolding predicates

**Form:** `unfold(name)`

**Core.** Make the predicate `name` transparent for the rest of this proof
branch. Every available fact that mentions it gains its one-layer body, the
current goal is rewritten the same way, and a later goal that mentions it is
read through its body too. The argument is the predicate's name, not one call:
every instance opens together, found through the per-predicate fact index.

**Accepts** the name of any declared `predicate`, in a pure theorem or a C
proof:

- Each available fact mentioning `name`, anywhere inside it (a conjunct of a
  requirement, under a quantifier or implication), gains a copy with every
  application replaced by the body at its arguments. The original fact stays.
- The current goal is rewritten the same way, including an application inside
  an `and`.
- A later goal of the same branch, such as a `have` goal, reads through the
  body too.
- A predicate mentioned nowhere is accepted and only marks the name
  transparent.

**Outside it**, with what to write instead:

- A predicate the body calls: it stays opaque; `unfold` it as well.
- A pure function or a resource name: use `unfold(f(args))` or
  `unfold(resource(args))`.
- Transparency outside the `have` that unfolded it: `unfold` again there.

**Failure, checking, and tools:**

An unknown name, including a resource's, fails with ``unknown predicate
`name` ``. An `unfold` inside a `have` ends with it: the predicate is opaque
again afterwards. Click opens exactly the named predicate layer; expansion is
unchanged, and profiling charges the produced proposition.

**Checked examples:** [`sorted_predicate.md`](https://github.com/clicklang/click/blob/master/mdtests/sorted_predicate.md), [`simple_statement_step_explicit_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_explicit_transport.md)

### Unfolding resources

**Form:** `unfold(resource(args))`

**Core.** Replace the exact held composite resource with one supported body
layer. For an `authorized` family it destroys one member and requires that
family's owned `authority(...)`; `unfold(authority(R(..)))` retires a population
whose count is zero. `let { slot: name, ... } = unfold(resource)` names the
opened children and C-typed fields; it is the one binding form.

On a declared resource the slots are the body's `let ... where` witnesses, bound
to the values the body binds them to, so a later `fold` spells a body fact over
a witness with its name
([`unfold_names_a_witness_for_a_fold_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_names_a_witness_for_a_fold_body_fact.md));
this form needs an execution frontier before function exit.

**Accepts** a declared resource with a body that the current state holds
directly, owned or viewed, in a C function proof (at the execution frontier
before exit, or at a function outcome after the C has returned) or in a `tactic`'s
`by` block:

- The arguments name the held instance up to equality by current facts:
  under `requires p == q;`, `unfold(cell(q))` opens a held `cell(p)`.
  `unfold(name)` on an instance binding opens that instance, its field names
  denoting the instance's fields.
- The body's `if` guard, or its `match` arm, must be decided by current facts;
  a decided false guard opens an empty body.
- It consumes the folded fact and adds each clause of the selected body as a
  held fact: owned memory, owned child resources (still folded: open each with
  its own `unfold`), and an iterated ownership fact. Each body `fact` becomes
  an available fact. A viewed composite opens to views of its body, which
  grant no write.

**Outside it**, with what to write instead:

- A resource held only inside another folded composite: `unfold` the parent
  first; one `unfold` opens one layer.
- An abstract resource (no body): nothing opens it; a contract consumes it.
- An undecided guard or arm: establish the guard or its negation first, with
  `have`, a `requires`, or a C branch.
- Inside `have ... by { ... }` or another fixed-state proposition proof: run
  `unfold` at the frontier before the `have`.
- Reading one layer without consuming it: `observe(resource)`.
- A predicate: `unfold(name)` with the predicate's name.

**Failure, checking, and tools:**

An unknown or absent resource, bodyless definition, or undecided guard fails. A
trailing `unfold(resource) as { ... }` map is refused with the `let` form to
write. Click opens exactly one resource layer; expansion is unchanged, and
profiling charges the produced body.

**Checked examples:** [`composite_resource_composes_token.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_composes_token.md), [`unfold_names_its_pieces_on_the_left.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_names_its_pieces_on_the_left.md), [`conditional_resource_unfold_requires_decided_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/conditional_resource_unfold_requires_decided_guard.md), [`composite_resource_once_flag.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_once_flag.md)

### Folding resources

**Form:** `fold(resource)`

**Core.** Check the current pure body facts without searching the proof context,
consume the contained resource facts, and produce the named composite resource.
Pure facts remain available. Folding a definition whose body views memory makes
the head hold that borrow open until the head is unfolded or consumed.

For an `authorized` family it creates one member and requires that family's
owned `authority(...)`; `fold(authority(R(..)))` establishes an empty
population. `let name = fold(resource, { field: value }, { slot: child })`
constructs an instance with fields from the named children; a child whose owned
resource has the slot's own name may be left out of the map, and a map left
empty is left out.

An instance name a proof binds, by `let name = fold(...)`, `unfold` or a call,
names its instance only to the end of the block that holds it, like every other
proof binder. The resource itself stays in the proof state after the block. To
name it after the block, bind it before the block or name it in the contract:
arms that `let d = fold(...)` a contract's `produces d` fill that instance.

**Accepts** a declared resource with a body, in a C function proof (at the
execution frontier, or at a function outcome after the C has returned) or in a
`tactic`'s `by` block, when:

- The body's `if` guard, or its `match` arm, is decided by current facts; a
  decided false guard folds an empty body.
- Each resource clause of the selected body is held directly: owned memory,
  including a subrange of a larger owned range (the rest stays held); a folded
  child resource; the iterated ownership fact with nothing taken out. Arguments
  match up to equality by current facts: under `requires p == q;`,
  `fold(cell(q))` consumes `p`'s cells.
- Each body `fact` is proved by its written obligation proof or by ordinary
  implicit `solve()`. An already-known fact is still an obligation.

It consumes the clauses' facts and adds the folded resource; the pure facts
stay. Each body fact without a written proof goes to the implicit closer
described below, which is smart: its miss is not a `fold` bug.

**Outside it**, with what to write instead:

- A child held only inside another folded composite: `unfold` that parent
  first.
- A body fact the implicit closer cannot prove: state it with
  `have ... by { ... }` first, or prove it at the fold with `fold(...) by` or
  `fold(...) { requires P by ...; }`.
- An undecided guard or arm: establish the guard or its negation first.
- An abstract resource (no body): a contract's `constructs` clause and
  `construct(resource)` create a token.
- Inside `have ... by { ... }` or another fixed-state proposition proof: fold
  at the frontier before the `have`.

**Failure, checking, and tools:**

Every body fact is an obligation, including exactly available and trivially
true facts. The driver uses its written proof or ordinary `solve()`, and
expansion retains that proof. A failed proof names the body fact.

A body fact over a witness the proof cannot name has no requirement spelling, so
the fold is refused at it; the fold never searches. A missing body member, false
body fact, or undecided guard fails. A slot is taken by name only for the arm
the model selects, only from an owned, folded resource of the slot's family, and
never from the fold's own result; otherwise the fold names the missing child.

Click folds exactly the named resource, completing the child map before the
kernel checks it; expansion keeps a bare fold unless the implicit closer proved
a body fact, and profiling charges its body.

**Checked examples:** [`composite_resource_composes_token.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_composes_token.md), [`a_fold_takes_children_by_name.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_takes_children_by_name.md), [`a_fold_does_not_take_an_unfolded_child_by_name.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_does_not_take_an_unfolded_child_by_name.md), [`a_fold_does_not_take_a_child_of_another_family_by_name.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_does_not_take_a_child_of_another_family_by_name.md), [`fold_proves_an_unstated_body_fact_by_implicit_solve.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_proves_an_unstated_body_fact_by_implicit_solve.md), [`a_block_bound_instance_name_ends_with_its_block.md`](https://github.com/clicklang/click/blob/master/mdtests/a_block_bound_instance_name_ends_with_its_block.md), [`an_instance_bound_before_a_block_is_named_inside_it.md`](https://github.com/clicklang/click/blob/master/mdtests/an_instance_bound_before_a_block_is_named_inside_it.md)

### Folding with one obligation

**Form:** `fold(...) by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
an open body fact a different proof than the implicit closer. Any `fold` form
followed by the proof of its one body fact, written as
the resource's body fact over the fold's arguments and proved at the fold, as a
`have` would.

The body is one tactic call, such as `solve();`, or a block.

**Failure, checking, and tools:**

Refused when the selected body has no fact obligation (superfluous) or more than
one; the second refusal spells each as a `requires` entry to copy. `fold(...) by
auto` is a syntax error: it means `fold(...)`. Expansion keeps the `by` and
prints the body's checked steps.

**Checked examples:** [`fold_by_proves_its_one_open_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_by_proves_its_one_open_body_fact.md), [`fold_by_proves_an_already_known_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_by_proves_an_already_known_body_fact.md)

### Folding with several obligations

**Form:** `fold(...) { requires P by ...; }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
several open body facts their own proofs. Any `fold` form followed by one
`requires [label:] P by ...;` entry per body fact it proves. Each `P` states
exactly one body fact; one no entry writes goes to the
implicit closer.

**Failure, checking, and tools:**

An entry that states no open body fact, or repeats an earlier entry's, fails
where it is written and lists the open body facts. Expansion keeps each entry
and prints its body's checked steps.

**Checked examples:** [`fold_requires_proves_each_open_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_requires_proves_each_open_body_fact.md)

### Constructing resources

**Form:** `construct(resource)`

**Specialized.** Write it at a function outcome whose contract `constructs` an
abstract token. At a function outcome, create exactly one owned abstract token
named by an authorized `constructs` clause without consuming an input resource.

**Accepts**, at a function outcome (after the last `step()` or `step_until(function.exit)`),
an owned `abstract resource` token declared without `authorized`, when:

- One of the function's `constructs` clauses, evaluated at that outcome,
  denotes the same token: the same family and the same argument terms.
  Arguments that evaluate to the same term qualify, so `construct(tok(n))`
  matches `constructs tok(result);` on a path that returns `n`.
- No identical token is already held.

It adds the token; nothing is consumed.

**Outside it**, with what to write instead:

- Before the outcome: step to the exit first with `step()` or `step_until(function.exit)`.
- A composite resource (one with a body): `fold` it from its body.
- A member of an `authorized` family: `fold` it with the family's authority.
- A token whose arguments are equal to a clause's only by arithmetic, such as
  `tok(1 + n)` for `constructs tok(n + 1);`: spell the arguments as the clause
  does.
- A token no `constructs` clause names: add the clause to the contract.

**Failure, checking, and tools:**

A non-token, composite, duplicate, unauthorized, or pre-execution construction
fails, as does construction of an `authorized` family, whose members only `fold`
creates. Click checks the exact zero-source resource transition in the kernel;
expansion preserves the checked step, and profiling charges one simple leaf.

**Checked examples:** [`contract_tests.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/contract_tests.rs), [`authority_ordinary_token_construction.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_ordinary_token_construction.md), [`authority_authorized_token_construction_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_authorized_token_construction_rejected.md)

### Taking a range

**Form:** `take(base[a..b])`

**Specialized.** Write it to use one element of an iterated ownership fact as
ordinary owned memory. Move one element out of the unfolded iterated ownership
fact whose elements live at `base`, as ordinary owned memory. The element's
index must be known in range, its guard known true, and the index not already
out; the fact then claims nothing at that index.

**Accepts**, at a C function's execution frontier before exit, a range that is
one element of the one held iterated ownership fact whose elements live at
`base` (the declaring resource already unfolded), when:

- The range is the clause's element at some index `i`: for
  `owns data[k..k + 1]` write `data[i..i + 1]`; for an offset clause
  `data[k + 1..k + 2]` write `data[i + 1..i + 2]`; for a stride `s > 1`
  write `data[s * i + a..s * i + b]`, with the offset in any spelling of the
  same affine form (`i * s`, `s * i`, or `i + i` for `s = 2`). `i` may be any
  `int32` term, constants included.
- `lo <= i` and `i < hi` are settled by the kernel's condition decision from
  current facts: stated bounds, equalities (`j == index`), and chains of
  bounds (`0 <= j`, `j <= index`).
- The guard at `i` is settled true the same way, from a fact about the guard
  cell (`occupied[i] == 0`, or `occupied[i] <= 0` with `occupied[i] >= 0`)
  or from a C branch on it. Both `g[k] == v` and `g[k] != v` guards work.
- `i` is settled different from every index already taken out.

It adds the element as owned memory and records `i` as taken out. Several
elements may be out at once.

**Outside it**, with what to write instead:

- A range wider or narrower than one element, such as `data[i..i + 2]` for
  a one-cell clause: one `take` per element.
- An iterated fact still folded inside its resource: `unfold` the resource
  first.
- An index whose range, guard, or distinctness is not settled: state it with
  `have` or a `requires` first; a guard known false holds no element.
- After the function exit: take before execution reaches the exit.

**Failure, checking, and tools:**

An unknown or false guard, an index that may already be out, an index not
known in range, a range that is not one element, or two held iterated facts at
the same base fails, each with its own message. The kernel re-derives the step
from its input state when the trace is checked; expansion prints it unchanged,
and profiling charges one guard cell and the fact's taken-out indices.

**Checked examples:** [`iterated_ownership_allocate_one.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_allocate_one.md), [`iterated_ownership_rejects_take_false_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_rejects_take_false_guard.md), [`iterated_ownership_rejects_take_unknown_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_rejects_take_unknown_guard.md), [`take_refuses_an_element_already_taken_out.md`](https://github.com/clicklang/click/blob/master/mdtests/take_refuses_an_element_already_taken_out.md), [`take_refuses_a_range_that_is_not_one_element.md`](https://github.com/clicklang/click/blob/master/mdtests/take_refuses_a_range_that_is_not_one_element.md)

### Giving a range

**Form:** `give(base[a..b])`

**Specialized.** Write it to return an element taken with `take`. Move a
taken-out element back into its iterated ownership fact. Its guard must be known
true.

**Accepts**, at a C function's execution frontier before exit, a range that is
one element of the one held iterated ownership fact at `base`, spelled as for
`take`, when:

- Its index is settled equal to an index taken out of the fact, by `take` or
  by a C store that made the guard true.
- The guard at that index is settled true by the kernel's condition decision.
- The element's cells are owned.

It consumes the element and clears the index from the taken-out set.

Both `give` and `take` accept an explicitly saved pointer base:
`give(at(opened, arena->data)[i..i + 1])` or `take(old(data)[i..i + 1])`.
Only the base expression selects an earlier state. Bounds outside that selector
refer to the current state, and guard checking and ownership transfer occur in
the current state. This selects the recorded base directly when a fresh read
of a descriptor field does not find its iterated ownership fact; it does not
search for equivalent pointer spellings.

**Outside it**, with what to write instead:

- An element never taken out: there is nothing to return; the fact already
  holds it.
- A guard known false or not settled: store the guard value in C, or state
  the guard cell's value as a fact first.
- After the function exit: give before execution reaches the exit.

**Failure, checking, and tools:**

A guard that is false or unknown, or an element that is not out, fails. Checked
and expanded like `take`.

**Checked examples:** [`iterated_saved_base_release.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_saved_base_release.md), [`iterated_saved_base_current_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_saved_base_current_bounds.md), [`iterated_ownership_release_one.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_release_one.md), [`iterated_ownership_rejects_give_false_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_rejects_give_false_guard.md)

### Gathering resources

**Form:** `gather(resource(args))`

**Specialized.** Write it to form an iterated ownership fact from the range it
covers. Form the iterated ownership fact the named resource's clause denotes:
from the owned range its elements cover when a quantified fact says every guard
is true, or from nothing when every guard is false.

The guard cells must be owned.

**Accepts**, at a C function's execution frontier before exit, a declared
resource whose body has an iterated clause over `lo..hi`, instantiated at the
written arguments, when:

- The guard cells of the whole range are owned.
- Every guard is settled one way: the guard at a fresh index `k` with
  `lo <= k` and `k < hi` is decided by the kernel's condition decision after
  instantiating each `forall (k: int32) { A implies B }` fact once. A fact
  `forall (k: int32) { lo <= k and k < hi implies occupied[k] == 0 }`, one
  over a wider range, or one stating the negation (`occupied[k] != 0`,
  `occupied[k] == 1`) qualifies.
- When every guard is true, the elements tile one range
  (`b - a == s` in `base[s * k + a..s * k + b]`) and that range
  `base[s * lo + a..s * hi + a]` is owned, possibly inside a larger owned
  range.

It consumes the covering range (nothing when every guard is false) and adds
the iterated fact with nothing taken out, as an `unfold` of the resource would
expose it; `fold` then forms the resource.

**Outside it**, with what to write instead:

- Guards mixed or not settled by one instantiation, including a curried
  `forall (k: int32) { lo <= k implies (k < hi implies guard) }`: state the
  conjoined form with `have` first.
- Gapped elements (`b - a < s`) with true guards: there is no single covering
  range to gather from. With every guard false, `gather` forms the gapped
  fact from nothing.
- A resource without an iterated clause: `fold` it.
- After the function exit: gather before execution reaches the exit.

`gather` does not check that the same fact is already held: with every guard
false, gathering twice holds two empty facts. That is not a guarantee.

**Failure, checking, and tools:**

Guards that are not all known one way, an unowned guard range, or an unowned
covering range fails. The kernel instantiates the quantified guard fact once at
an arbitrary index; the range is never enumerated.

**Checked examples:** [`iterated_ownership_gather_scatter.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_gather_scatter.md), [`iterated_ownership_gather_fresh_heap_map.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_gather_fresh_heap_map.md), [`iterated_ownership_rejects_gather_unknown_guards.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_rejects_gather_unknown_guards.md), [`gather_refuses_elements_that_do_not_tile_a_range.md`](https://github.com/clicklang/click/blob/master/mdtests/gather_refuses_elements_that_do_not_tile_a_range.md)

### Scattering resources

**Form:** `scatter(resource(args))`

**Specialized.** Write it to dissolve an iterated ownership fact back into its
range. The converse of `gather`: consume the named clause's iterated fact, with
nothing taken out, and return the covering range when every guard is true, or
nothing when every guard is false.

**Accepts**, at a C function's execution frontier before exit, a declared
resource whose body has an iterated clause, when the iterated fact that clause
denotes at the written arguments is held with nothing taken out, and every
guard is settled one way as for `gather`. When every guard is true the
elements must tile one range, which it adds as owned memory.

**Outside it**, with what to write instead:

- A fact with an element taken out: `give` it back first.
- A fact still folded inside its resource: `unfold` the resource first.
- Guards not settled one way: as for `gather`.

**Failure, checking, and tools:**

As for `gather`; a fact not held, or held with an element out, fails with
"scattering needs the iterated ownership fact with no element taken out".

**Checked examples:** [`iterated_ownership_gather_scatter.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_gather_scatter.md)

### User-defined tactic calls

**Form:** `name(args, { binder: instance })`

**Specialized.** Write it to apply a `tactic` the project declares, such as a
resource reshaping lemma. Apply the user-defined tactic `name` at the current
execution frontier, before the function exits: bind each of its supplied
resource binders to an instance the proof holds, check its `requires` as
available facts, consume its consumed instances, produce its produced instances
under the names of a `let { binder: name }` pattern, and add its `ensures`.

No C runs and memory is unchanged, so every fact about a cell survives.

Evaluation prerequisites of argument expressions are ordinary obligations. Supply
`by { ... }` for one or `{ requires P by ...; }` for several; omitted proofs use
implicit `solve()`. Expansion retains these proofs (see
[`tactic_argument_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/tactic_argument_obligation.md)). This does not change the
exact-fact requirements of the tactic contract itself.

**Accepts**, at the execution frontier of a C function or `tactic` proof
before exit, an application of a `tactic` declared earlier in the module (or
the tactic itself, for recursion), when:

- There is one argument per parameter: any C-valued expression over the
  frontier (`n + 1`, constants), and the literal `0` at a pointer parameter.
- The map names every instance binder the tactic's `consumes`, `owns`, or
  `views` clauses declare, each mapped to an instance of the binder's
  resource that the proof holds. The map is left out only when the tactic
  declares no such binder; an instance of the binder's own name is not
  picked up without it.
- Every `produces` binder is named by the `let { binder: name }` pattern.
- Each `requires`, at the arguments, is an available fact or a condition the
  kernel's condition decision settles (`n == 3` and `n >= 3` both discharge
  `requires t > 0;` at `t = n`). A recursive application also owes its
  `decreases` measure's descent this way.

It consumes the mapped consumed instances, adds the produced ones under the
`let` names, and adds the `ensures` facts.

**Outside it**, with what to write instead:

- A requirement only a proof establishes: prove it with `have` first.
- An instance an earlier step consumed, including an earlier application:
  it is gone; bind the instance that step produced.
- Inside `have ... by { ... }`, or after the function exit: apply it at the
  frontier before the `have` or before execution reaches the exit.

**Failure, checking, and tools:**

A missing requirement is refused by name, as are a map entry naming an unknown
binder or an instance of the wrong resource, and an application after function
exit. Click applies the tactic's certified contract once; expansion leaves it
unchanged, and profiling charges one application.

**Checked examples:** [`user_tactic_reshapes_owned_resources.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_reshapes_owned_resources.md), [`user_tactic_application_owes_its_requirements.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_application_owes_its_requirements.md), [`user_tactic_binder_map_checks_the_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_binder_map_checks_the_resource.md), [`user_tactic_consumes_its_inputs.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_consumes_its_inputs.md), [`user_tactic_after_exit_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_after_exit_is_refused.md), [`user_tactic_accepts_null_pointer_arguments.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_accepts_null_pointer_arguments.md), [`user_tactic_recursion_converts_a_list.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_recursion_converts_a_list.md)

### Observing resources

**Form:** `observe(resource)` or `observe(p[lo..hi])`

For an explicitly selected memory range, `observe(p[lo..hi])` adds
`viewable(p[lo..hi])` at the current program state. The exact range must be
held as a unit owner or view. This form also works at function exit and
inside a `have` proof with a concrete program state. It performs indexed
permission lookups, without looking for a covering range or following
history. The held resources do not change.

This establishes live storage, not initialized contents or any stored value.
To restrict the resulting fact to a smaller range, use `separation::contains_subrange`
and `separation::viewable_restrict`. For example, see
[`observe_memory_after_store.md`](https://github.com/clicklang/click/blob/master/mdtests/observe_memory_after_store.md).
[`observe_uninitialized_memory_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/observe_uninitialized_memory_rejected.md)
checks that a subsequent `solve` still cannot establish initialization.

The remaining rules in this section describe observing a declared composite
resource.

**Specialized.** Write it to read a folded resource's view and facts without
unfolding it. Keep a held composite folded while projecting its declared
non-consuming view and immediate facts.

**Accepts**, at a C function's execution frontier before exit, a declared
resource with a body that the current state holds owned or viewed, its
arguments matched up to equality by current facts, when its guard or arm is
decided:

- It adds each body `fact` as an available fact, and a view of each
  contained clause: views of owned memory, so C may read but not write it,
  and a viewed child resource, which a further `observe` reads one layer
  down.
- The resource stays held and folded; repeating `observe` is harmless.

**Outside it**, with what to write instead:

- Writing the body's memory, or consuming a child: `unfold` it.
- A resource not held, including one held only inside another composite:
  `observe` the parent first, one layer per step.
- After the function exit, or inside `have ... by { ... }`: observe at the
  frontier before.

An `observe` whose guard is undecided currently succeeds and adds nothing.
That is not a guarantee; decide the guard first.

**Failure, checking, and tools:**

An absent resource or unsupported projection fails; owned contained resource
facts never leak. Click performs one projection layer, expansion is unchanged,
and profiling charges that layer.

**Checked examples:** [`composite_resource_folded_nested_fact_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_folded_nested_fact_projection.md), [`composite_resource_observe_nested_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_observe_nested_fact.md)

## Expansion, profiling, and audit

`click expand` replaces a selected smart tactic with its checked explicit
proof. Expanded proofs use only canonical surface names; internal
Rust variants such as certified statement transitions are not a second user
vocabulary. Expansion starts from a correct selected proof unit and verifies
that complete proof unit again after rewriting it. It does not emit a partial
rewrite when a later tactic in the same proof is failing.

Expansion removes the selected tactic's avoidable planning and search cost; it
does not remove the unavoidable work of checking the emitted operations or
reading the longer explicit proof. A smart hotspot should therefore become
approximately as cheap as its direct checked proof permits. A materially slow
simple leaf is an engine defect rather than another expansion opportunity.

`click expand --claim LABEL` applies the same checked rewrite to every smart
tactic in one function claim. This avoids manual site-by-site work when the
aggregate search cost is significant even though each smart tactic is prompt.

`click profile` reports smart and simple work under the same concepts:
statement transitions are `step`, checked loop transitions are `loop`,
fact transports are `transport`, and atomic
reasoning uses rules such as `known`, `normalize`, `rewrite`, and named
theorem applications. A slow simple leaf is a Click performance bug. A
successful slow smart tactic is an expansion candidate. An unsuccessful smart
tactic has nothing to expand; decompose that proof unless its search failed to
respect its bound or expose an actionable next step.

`click audit` finds smart tactics in a project, expands each one, and verifies
the rewritten source. Its purpose is to detect missing or invalid expanded
proofs, not to promise constant total verification time as a project
grows.


## Arithmetic bridge prerequisites

`solve` carries connected machine comparisons into mathematical `Integer`
comparisons through checked standard-library theorems. When observing an
addition or subtraction requires its own definedness or no-wrap bound, a
nested search does not re-enter the same operation's bridge. Already available
prerequisites can still justify the observation; a cyclic attempt is a search
miss. No stack size or work budget is raised.

[UInt64 successor with an additional bound](https://github.com/clicklang/click/blob/master/mdtests/uint64_successor_solve_with_additional_bound.md)
checks that an extra machine bound does not make an arithmetic proof recurse
indefinitely. Its false-small-bound companion keeps an unprovable conversion
bound rejected.
