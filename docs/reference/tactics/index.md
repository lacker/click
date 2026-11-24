# Proof tactics

This page is the reference inventory of the tactics in Click's specification
language. A tactic is either **smart**, **simple**, or **control**:

- Smart tactics search. They include the fallback search in `close()`,
  `close() using`, and `step_until`, which steps to a target and proves what
  each step needs. Smart tactics also include the implicit closer, which
  ends proofs including loop `maintain` scripts and finishes a `step()` or
  `fold`, and forms whose search fills an elided argument:
  `apply(fact)`, `apply(ih(m))`, and a bare `transport(P, Q)`. They
  are the tactics that `click profile` may recommend expanding. The parser
  refuses retired forms such as `known()` and `solve()` and names their
  replacement, `close()`.
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
distinction for its `tactic-bug` outcome.

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
- `step_until(point)`: run to one statement, loop, or `function.exit`
  without splitting. See [Execution](#execution).
- `branch { true => { ... } false => { ... } }`: prove each arm of the C `if` at the
  frontier. See [Execution](#execution).
- `loop { ... }`: prove a C loop from its invariants, which the back edge
  closes member by member with `close()`. See [Execution](#execution) and
  [Resources and transport](#resources-and-transport).
- `close()`: close the first open goal. Use `close() using { ... }` to
  close it from the listed premises. See [Automation and search](#automation-and-search)
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
- `let ih = induct(value)`, with `apply(ih(m))`: prove
  a pure theorem by induction. See
  [Proposition reasoning](#proposition-reasoning).
- `rewrite(from, to)`: rewrite the goal with an available equality. See
  [Proposition reasoning](#proposition-reasoning).
- `contradiction(P)`: close an impossible case from a fact and its negation.
  Use `contradiction()` when the context already establishes `false`.
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
- **Closing a proposition.** Let the implicit closer finish the script,
  or write `close()` to close the first open goal and continue. Use
  `close() using { ... }` to restrict proof search to listed facts.
  For a proof that must replay without search, use `click verify --checked-only`.
- **Equalities and states: `rewrite`, `transport`.** `rewrite(from, to)` is the
  default: it rewrites the goal with an equality at the current state.
  `transport(P, Q)` carries a fact stated at an earlier state to the current
  one when `step` did not carry it; its `using` form, which lists the frame
  evidence, is expansion output. `close()` tries both within its bounds.
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
  proposition. `cases` checks that its written alternatives cover the path.
  `match` splits on constructors and `branch` follows a C `if`. Tactics written
  after a proof `if`, `cases` or `match` are checked once: the arms rejoin,
  keeping the facts every arm proved, or the split is refused. An arm that
  reaches function exit is a finished path, like each `return` of the C: the
  implicit closer that ends the proof closes its remaining goals on that
  path, so a split that ends a proof finishes each arm on its own.

## Automation and search

Every proof script ends with an implicit tail, and an omitted proof clause is
that tail alone. The tail runs the C the script leaves, splitting at each C
branch the facts do not decide into paths that each run to function exit,
and then closes every open claim on every path with the implicit closer, per
claim or once for a grouped proof. A written `close()` closes the first open goal and runs no C, so
`by close();` restates the omitted proof only where no C is left to run, as
for a pure theorem or a `have`; with C left it is refused, since its goals
exist only at function exit. The implicit closer tries direct logical closure on each open claim,
then bounded proof search. On a returned path that holds the body of a resource
the contract produces, it first tries to fold the body, as `fold(R(...))` after the C
would; a fold that does not check leaves the path as it was
(`mdtests/an_omitted_proof_folds_the_resource_its_contract_produces.md`). A proof
script that ends with a claim still open closes it the same way, so a script
needs no final closer and no final step to function exit. The body of a `with` scope is
the exception: the scope closes where its body ends, before the tail runs, so
a body that must reach the function's return steps there itself with
`step_until(function.exit)`. On a stated fact,
`have P by close();`, there is no C to execute.

On an arithmetic goal that its indexed derivations miss, `close()` runs
arithmetic from premises it selects itself: the facts connected to the goal,
and the type ranges of the machine values they observe. It also carries
connected machine orders to `Integer`, proves a machine order through its
`Integer` reading, an equality from its two bounds, and `defined(a + b)` from
the bounds of the exact result (see
[intermediate facts](#intermediate-facts)). A loop bundle member, which may
cite only the loop head and the contract, selects nothing. When its other
strategies miss, `close()` works from the facts connected to the goal. It reads a condition a function
fact forces out of the function's definition
(`mdtests/solve_reads_a_condition_out_of_a_definition.md`), then rewrites the
goal by the connected equalities: first a goal that
restates an available fact through one connected equality, such as
`f(Node(..)) == 1` beside `f(t) == 1` and `t == Node(..)`, by one `rewrite`
and `close()` (at most 16 rewrites), then a bounded chain of up to three
rewrites whose rewritten goals the direct closers and a nested `close()` try.
Last, it states the equation between two constructor applications that facts
equate to one value, and reads the fields' equalities, or the constructors'
mismatch, from it
(`mdtests/solve_reads_definitions_and_constructor_equations.md`).
Written
as a step of a script, `close();` closes the first open goal
(`mdtests/a_written_solve_closes_one_goal.md`). A
script that stops with C left ends with the implicit tail, which executes
whatever remains and closes every open goal
(`mdtests/a_script_that_stops_after_explicit_steps_executes_the_rest.md`). In
each arm of a proof `if` that ends a proof, the arm's own closer closes that
arm's goals
(`mdtests/solve_closes_each_arm_of_a_split_that_ends_a_proof.md`). Successful smart tactics and the implicit closer retain the checked
surface evidence that `click expand` can render as an explicit proof.
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
`step_until` runs drops such an element, the tail writes that disequality
from the two index words, `((m - 1) as int32) != 0`,
`((n - 1u64) as uint64) != 0u64` or `j != 0u64` say,
proves it at the statement's pre-state, retains it as a `have`,
and runs the statement again, which then keeps the element. It tries at most
four dropped elements per statement, and proves each only by the signed
interval certificate over its variables' bounds, an order between the two
indices by selected-premise arithmetic, or the disequality bridge of
[`close()`'s arithmetic](#arithmetic-with-selected-premises) (a case split on the index
equality), not by the rest of `close()`. Bounds such as `2 <= m` or `1 <= j`,
`1 <= m` with `m != 1` (a bound made strict by a disequality of its own
difference,
[`a_store_index_bound_and_disequality_keep_a_cached_element.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_index_bound_and_disequality_keep_a_cached_element.md)),
or the Integer fact `m - 1 != 0` where `m - 1` cannot wrap, suffice. Expansion writes the `have` before the
statement's `step()`. A disequality it misses leaves the statement as it
ran. The path keeps the miss (at most 32 per path): a later refusal whose
goal reads the dropped element names the statement and the disequality the
tail wrote, ``statement(3) may have overwritten `q[0]`; it is kept if you
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
the fact is first restated as a `have` by rewriting with that equation. The
expanded proof uses `close()` if the goal already holds. When it needs to split a
condition before reaching the goal, it writes a proof `if`. At each end, expansion proves an equation between the application and
the selected branch's literal using `unfold`, selected arm equations and
`close()`. It rewrites the claimed value comparison with the equation and
closes the branch with `contradiction`. At most 16
connected function facts are read, each up to 16 ends; a `match` that its
arguments do not decide, or an end that is not a constant, is a miss. See
[`solve_reads_a_condition_out_of_a_definition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_reads_a_condition_out_of_a_definition.md)
and
[`solve_does_not_read_an_unforced_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_read_an_unforced_condition.md).
The function may be generic, and `bool`-valued with `true`/`false` ends: the
fact `list::contains(xs, x)` reads as `== true`, and is refuted by
`have not list::contains(xs, x)`. An end that applies a defined function, as
`list::contains(Nil, x)`, is followed into that definition (at most 4 deep)
and unfolded after the fact's own application. A condition written other than
the goal, `v == x` against a postcondition's `result == x`, matches when it
lowers to the same goal. So `list::contains(Cons(v, Nil), x)` forces `v == x`
([`solve_reads_a_condition_out_of_a_generic_bool_definition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_reads_a_condition_out_of_a_generic_bool_definition.md),
[`solve_does_not_read_an_unforced_generic_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_read_an_unforced_generic_condition.md)).

Signed `int32` arithmetic substitutes equalities: `x == 5` bounds `x` on
both sides, so it proves `x - 1` defined and closes `x - 1 == 4`; a listed
`a == b + 1` with `b` bounded converts to `a - b == 1` and bounds `a`, and
`c == a + 1` converts after it. A bound substitutes through such equalities
in turn to the listed bounds on what remains. `close()` gathers a goal
variable's equalities beside its bounds when the bounds alone decide
nothing, so a callee's `ensures o.size == old(o.size) + delta`, about a
resource field or a cell, supports arithmetic across calls (see
[`arithmetic_using_chains_equalities.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_using_chains_equalities.md)
and
[`abstract_resource_field_call_facts_support_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/abstract_resource_field_call_facts_support_arithmetic.md)).

For a signed `int32` bound, `close()` can use an indexed equality of a goal
operand to a literal even when that call-derived equality has no recorded
Surface form. It first proves the equality in a checked nested `have`
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

When a call's generated pointer has no source struct layout, expansion writes
an indexed array field as an explicit typed read at its byte address. This
retains the field offset and element width when reparsed; it grants no read
authority. Named struct pointers and library model accessors retain their
ordinary form. The Rust
assignment-operator audit checks this through an erased local array pointer.

For equality of a 32-bit or 64-bit machine integer with a literal, `close()` and
the implicit closer stop searching when current facts already decide the opposite truth
value. An inconsistent context remains eligible for contradiction closure.
The reference-call scaling regression compares valid results with false
literal results over four sizes; refusal does not print every old call fact.

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
smaller execution steps or exact premises; `close() using { ... }` constrains
pure search to named facts, while a shorter run of `step();` lines isolates
the one execution transition that fails.

## Execution

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `mark name;` | simple | Specialized | Name the current execution state. | [Reference](#proof-marks) |
| `step()` | simple | Core | Execute one checked statement transition. | [Reference](#single-statements) |
| `let { result: name } = step()` | simple | Specialized | Bind a checked assignment, call, or scalar step result. | [Reference](#binding-a-statement-result) |
| `step_until(statement(i).entry)` | smart | Specialized | Execute up to a selected source point, or to `function.exit`, without splitting. | [Reference](#execution-to-a-point) |
| `branch [ensuring { ... }] { true => { ... } false => { ... } }` | control | Core | Prove and join the arms of source control flow. | [Reference](#source-branches) |
| `loop [name] { ... }` | control | Core | Prove a loop from its invariants and ranking obligations. | [Reference](#loop-transitions) |
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
saved states that can be restored. In particular, `step_until(name.entry)` does
not target a proof mark.

Expansion of execution automation emits one `step();` line per executed
statement, followed by the outcome closers. Expansion recurses through `loop`
and materializes omitted phase proofs at the loop keyword.

### Proof marks

**Form:** `mark name;`

**Specialized.** Write it to name the current state so a later fact can refer to
it with `at(name, ...)`. At any live execution frontier, give the point the
path is at now a proof-local name without advancing C.

**Accepts** a name not yet marked on the current path, at a live frontier of a
C function's execution script: the claim's top-level script, a `branch` arm, a
proof `if` or `cases` arm, or a loop's `maintain` proof. It records the current
state under that name and changes nothing else:

- From then on `at(name, e)` reads `e` in the recorded state. It can appear in
  a `have`, a `branch ensuring` interface, or the `ensures` clause the script
  proves (`ensures result == at(after_first_write, x) + 1 by { ... }`).
- The name stays visible after later steps and after a `branch` join, and
  inside nested loop `maintain` proofs.
- The two arms of one `branch` or proof `if` may each mark the same name.

**Outside it**, with what to write instead:

- A name already marked on this path fails with `duplicate proof mark`. Choose
  another name.
- A name that is not yet marked, used in `at(name, ...)` before its `mark` or
  never marked, fails with `unknown proof mark`. Put the `mark` where the proof
  reaches that state.
- A mark made inside a `maintain` proof, read outside that proof, also fails
  with `unknown proof mark`. Loop invariants use `at(loop(n).entry, e)`.
- At function exit (after the last `step()` or `step_until(function.exit)`), `mark` is refused.
  Mark before the last step, or name the final values directly.
- Inside a `have ... by { ... }` body or a pure theorem, `mark` is refused.
  Write the mark in the execution script.
- A mark names a point the path has already reached, not a point in the C
  region tree that execution can be sent to. `step_until(name.entry)` does not target
  a mark; use `step_until(statement(i).entry)`.

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
body or ordinary implicit `close()`, even if the fact is already available.
An exact known precondition normally expands to `step() by { close(); }`.
This solving is smart and may miss; for example, it can prove a callee's
`requires a > 0` from `requires x == 5 or x == 7`.

Arithmetic evaluation still decides some safety conditions before generating
an obligation; migrating those decisions is separate remaining work. Pointer
subtraction and relational pointer comparison owe C's same-object
precondition this way: when the context does not decide it, the step emits
`same_allocation(left, right)` as an obligation at the operation, named by its
C rule, rather than a path of undefined behavior
(`mdtests/an_undecided_pointer_subtraction_owes_same_allocation.md`). An emitted
definedness requirement states the defined path's condition, such as
`s >= 0 and s < 32` for `x << s`. Unsigned divisor and float-to-integer
requirements in an operand of `&&`, `||`, or `?:` are conditional on the
facts from the condition that selects that operand.

The step produces one successor state:

- Assigned locals and stored cells hold the evaluated values. After
  `y = x + 1;`, `have y == x + 1 by close();` closes.
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

A direct safety refusal names the C operation, such as a read of an
uninitialized local. A documented modeling limit reports `unsupported`.
If Click generates a safety obligation but cannot prepare it for the
implicit closer, it reports an internal error. A refusal printed as `refused
by: the implicit closer that proves this statement's requirements` is a smart
miss. Prove
the printed `goal:` with `have` before the step, or prove it with
`step() by { ... }`. When the implicit closer cannot raise or prove an obligation, the
step is refused at that obligation. Requirement generation does not invoke
proof search; the driver runs the implicit closer.

An `assert`'s false-path obligation (as a Rust overflow check lowers to) is
written as the asserted condition at the pre-state, less any disjunct an exact
fact refutes.

Click carries no fact by list. Expansion leaves a step unchanged unless the
implicit closer proved an obligation. Then it prints `step() by { ... }` for
one obligation or `step() { requires P by ...; }` for several. Profiling
charges the step its one transition, and the implicit closer's work is a
separate smart `implicit closer` row at the step.

**Checked examples:** [`simple_statement_step.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step.md), [`simple_statement_step_branch_requires_exact_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_branch_requires_exact_fact.md), [`simple_statement_step_requires_exact_prerequisite.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_requires_exact_prerequisite.md), [`step_refuses_an_undecided_c_if.md`](https://github.com/clicklang/click/blob/master/mdtests/step_refuses_an_undecided_c_if.md), [`step_names_the_alias_cases_it_does_not_split.md`](https://github.com/clicklang/click/blob/master/mdtests/step_names_the_alias_cases_it_does_not_split.md), [`step_refuses_a_maybe_throwing_call.md`](https://github.com/clicklang/click/blob/master/mdtests/step_refuses_a_maybe_throwing_call.md), [`step_by_proves_its_one_open_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/step_by_proves_its_one_open_obligation.md), [`a_written_step_does_not_open_a_folded_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/a_written_step_does_not_open_a_folded_resource.md), [`smart_step_carries_prior_call_facts.md`](https://github.com/clicklang/click/blob/master/mdtests/smart_step_carries_prior_call_facts.md)

### Binding a statement result

**Form:** `let { result: name } = step()`

**Specialized.** Bind the checked value from the next assignment, call, or
scalar evaluation step to an immutable proof name. The name still refers to
that value after the program overwrites the local, leaves its scope, or uses
the step result.

**Accepts** a scalar or pointer local assignment such as `y = e;`,
`x += e;`, or the initializing assignment of `int32 y = e;`. It also accepts
a call whose result is used, including `y = g(x);`, `if (g(x))`, or
`return g(x);` at the call step. Bare `step()` must be able to resolve the
call in the current proof context. It also accepts a scalar value that the
front end retains in a separate step, such as a Rust load followed by an
arithmetic check. A proof name may be rebound, and the newest binding wins.

**Outside it**, with what to write instead:

- A call that needs a callee, contract, or binder selection: supply it on
  the right, for example `let { result: name } = step(g, { input: instance })`.
  Use the named call form to bind any resources the call produces.
- A call whose result C discards: use `step()`.
- A store through a pointer, field, or array element (`p[0] = 3;`,
  `p->v = 3;`): use `step()` and name the cell.
- A return step itself or a declaration's first step: use `step()`.
  In an outcome proof, `result` names the function's return value.
- A name that is a C variable here is refused with `names a C variable here`.
  Choose another name.
- An output other than `result`, such as `let { value: v } = step()`, is
  refused with `has only the result output`.

**Failure, checking, and tools:**

The ordinary step checks every access and arithmetic prerequisite, and the
binding adds no assumption. Expansion retains the binding unchanged.

**Checked examples:** [`c_static_function.md`](https://github.com/clicklang/click/blob/master/mdtests/c_static_function.md), [`step_binds_call_result_with_default_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/step_binds_call_result_with_default_resource.md), [`step_result_binding_names_checked_values_and_survives_overwrite`](https://github.com/clicklang/click/blob/master/src/surface/tests/project_tests.rs), [`a_step_result_name_can_be_bound_again.md`](https://github.com/clicklang/click/blob/master/mdtests/a_step_result_name_can_be_bound_again.md), [`step_result_binding_refuses_a_store_through_a_pointer.md`](https://github.com/clicklang/click/blob/master/mdtests/step_result_binding_refuses_a_store_through_a_pointer.md)

### Execution to function exit

**Form:** none; the implicit tail. The parser refuses the removed form
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
instance. `views` and `consumes` clauses make no claim. A closer (`close()`,
`normalize`, `all`, `close() using`) acts on the first
open goal, and a refusal names that goal; it does not look further down the
list for a claim it could close
(`mdtests/a_closer_after_execution_acts_on_the_first_open_claim.md`,
`mdtests/solve_after_execution_acts_on_the_first_open_claim.md`). The implicit
closer is the catch-all: it closes every goal still open.
`close()` closes a resource goal whose instance the path holds
(`mdtests/closers_after_execution_close_a_resource_goal_first.md`). A closer
written when every goal on the path is closed is refused
(`mdtests/a_closer_with_no_open_goal_is_refused.md`). `fold`, `apply`, `have`
and the other tactics that change the path's facts or resources act on the path
and leave the goal list alone; the implicit closer at the end of the script
closes the goals still open.

Goal refinements (`witness`, `intro` and `rewrite`) work on
the same first open claim. It must be a proposition, and the tactic applies to
its current goal. Close an earlier resource claim with `close()` to reach the
next claim. When a tactic leaves a claim on its own proof, later tactics
continue that proof using the path's current state and resources, so a later
`fold` or the contract's resource transition reaches it. A `have` written after
`intro` extends that proof. If a closer cannot handle the goal introduced by
`intro`, it can still close the original claim directly. A closer in a proof
opened only by `witness` must close the goal with the chosen witness.

A written `close()` or `close() using` must close an open goal. The implicit
closer at the end of the script
leaves an open claim to the report that names it
(`mdtests/a_written_solve_that_closes_nothing_is_refused.md`).

### Execution to a point

**Form:** `step_until(statement(i).entry)`

`step_until` repeats `step()` up to the target, walking any loop the facts
decide, and never splits: an undecided branch before the target refuses it, as
it refuses `step()`. The parser refuses the removed form `execute_until`
and names `step_until`.

**Specialized.** Write it to stop execution at a chosen statement, loop, or read
and do proof work there, instead of a run of `step();` lines. From a live
frontier, execute forward to the written program point. An entry uses the
same spelling as in `at(point, expression)`. Append `.entry` to a
statement or one of its subregions:
`step_until(statement(i).statement(j).entry)` stops before a nested statement and
`step_until(statement(i).call(f, j).entry)` stops just before one of its calls
(`mdtests/execute_until_runs_to_a_statement_region.md`);
`.assignment(x, j).entry` and `.read(j).entry` end a chain the same way, at the
statement's `j`th own store to `x` or memory load
(`mdtests/a_chained_region_ends_in_an_assignment_or_read.md`).
An ordinary scalar C call assignment has a call-result step followed by an
assignment step. A C aggregate call with a declared return type similarly has
a call-result step followed by a destination-copy step. Their `.call(...).exit`
and `.assignment(...).exit` name distinct points, even when both effects come
from one C statement (`mdtests/aggregate_call_and_destination_copy_have_separate_points.md`).
`step_until(region(N).entry)` stops before the `N`th atomic region;
`step_until(loop(N).entry)` selects the indexed loop entry;
`step_until(assignment(local, N).entry)` selects the Nth static local assignment
of the function before it executes.

`step_until(read(N).entry)` stops before the Nth statement of the function
containing an explicit scalar memory read. `step_until(loop.back_edge)`
finishes the current loop preservation region with checked steps; invariant
and ranking closure are separate. `step_until(loop(i).back_edge)` does the
same and is refused outside `loop(i)`'s preservation region
(`mdtests/execute_until_refuses_another_loop_s_back_edge.md`).

A construction-return proof may use `&result` before the return to name the
destination object. Its address alone supplies neither initialized field
values nor permission to read them. A program variable named `result` is
still available as `program::result`.

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

**Checked examples:** [`execute_until_runs_to_a_statement_region.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_runs_to_a_statement_region.md), [`execute_until_current_frontier.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_current_frontier.md), [`execute_until_selects_loop_entry.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_selects_loop_entry.md), [`execute_until_assignment.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_assignment.md), [`execute_until_read.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_read.md), [`execute_until_back_edge.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_back_edge.md), [`execute_until_back_edge_of_a_named_loop.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_back_edge_of_a_named_loop.md), [`a_chained_region_ends_in_an_assignment_or_read.md`](https://github.com/clicklang/click/blob/master/mdtests/a_chained_region_ends_in_an_assignment_or_read.md), [`step_until_steps_to_function_exit.md`](https://github.com/clicklang/click/blob/master/mdtests/step_until_steps_to_function_exit.md)

### Source branches

**Form:** `branch [ensuring { ... }] { true => { ... } false => { ... } }`

The `true` and `false` labels select the two outcomes of the C condition.
Write both arms in either order. An arm body may be empty, and commas
between arms are optional. An `ensuring` interface goes before the arm block.

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
join fails. Click follows the written arms and interface; expansion recurses
into smart descendants, and profiling classifies those descendants. Exported
facts retain outer proof-binding names for later `at(...)` rewrites, and reads
through local pointers keep their declared element types.

**Checked examples:** [`frontier_branch.md`](https://github.com/clicklang/click/blob/master/mdtests/frontier_branch.md), [`branch_interface_mixes_current_read_and_mark.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_mixes_current_read_and_mark.md), [`branch_interface_keeps_model_pointer_names.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_keeps_model_pointer_names.md), [`branch_interface_loaded_wide_pointer.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_loaded_wide_pointer.md)

### Loop transitions

**Form:** `loop [name] [diverges] { ... }`

**Core.** At a C loop frontier, prove initialization and one arbitrary
iteration, construct the loop rule, and advance to its abstract exit. One
iteration is a path that reaches the body's end, a `continue`, a `break`, or a
function `return`: a `continue` is the back edge; a `break` closes no invariant
and joins the loop's ordinary exits; and a `return` is terminal for the function
and owes neither the invariant nor ranking bundle.

A `maintain by { ... }` script works like a function proof. When it ends, or
when its tactics stop inside the body and the rest of the body runs implicitly
to the back edge (splitting at C `if`s like a function's implicit tail,
[`preserve_runs_the_rest_of_the_body.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_runs_the_rest_of_the_body.md)),
the back edge owes the loop's bundle: each declared `invariant`, guarded by
the invariants declared before it, and for a `decreases` loop one `0 <= m`
member per component and one descent member `m < at(<iteration entry>, m)`
(for a tuple measure, the right-nested disjunction over pivots with the
earlier components tied). Each member is closed by `close()`, exactly as a
function's exit closes each `ensures`; this closes, for example, an unsigned or
64-bit bound and its descent from the guard
([`back_edge_closes_an_unsigned_bound_from_the_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/back_edge_closes_an_unsigned_bound_from_the_guard.md)).
To help a member `close()` misses, prove it, or a fact it needs, with
`have <invariant> by { ... }` before the back edge. `click expand` prints the
closure as one `have <member> by { ... }` per member at the end of the
`maintain` script, omitting members already available as facts. The retired
`close_invariants` tactic is rejected by the parser
([`close_invariants_is_retired.md`](https://github.com/clicklang/click/blob/master/mdtests/close_invariants_is_retired.md)).

An optional `otherwise { ... }` block checks `have` statements at the
loop's false-guard exit. The block has no implicit goal. It sees the state
and facts on that exit, including the loop invariants available there.
Short-circuit guard paths join before the block. A false first test runs the
block before any iteration, a post-tested loop runs it after the body, and
a `break` exits through `maintain`. The checked facts from the block
contribute to the ordinary loop-exit join.

**Checked examples:** [Proving a fact on the false-guard exit](https://github.com/clicklang/click/blob/master/mdtests/loop_otherwise.md)
and [A break skips the block](https://github.com/clicklang/click/blob/master/mdtests/loop_otherwise_does_not_run_on_break.md).

Inside the loop's clauses and its `initialize` and `maintain` phases,
`iterations` is the mathematical
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
program variable of that name is [`program::iterations`](../language/index.md#program-binding-references)
([`a_c_local_named_iterations_is_written_program_iterations.md`](https://github.com/clicklang/click/blob/master/mdtests/a_c_local_named_iterations_is_written_program_iterations.md)).
Like any proof `Integer`, it compares with a C value directly, `i == iterations`
([`a_loop_pass_count_names_the_passes_after_the_loop.md`](https://github.com/clicklang/click/blob/master/mdtests/a_loop_pass_count_names_the_passes_after_the_loop.md),
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
judgment requires. A member `close()` misses fails locally, naming that member,
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
- A name outside the declared contracts must match the call's callee.
- Supply required input bindings in the map and name produced resources in the
  `let` pattern.
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

**Forms:** `step(callee)` and `step(callee, { binder: instance, n: value, ... })`.
Either can use a `let { result: name, binder: name, ... }` output pattern.

**Specialized.** Write it at a call whose callee declares instance binders,
to say which owned instance each binder takes; or `let` value parameters, to
give a value the caller cannot supply by holding an instance, such as the
length of the string a local array holds; or `produces` binders, to name the
instances the call creates. A declared named contract takes precedence. Other
names select the callee, which can be qualified, as in `step(unit::callee)`.
The C arguments come from the call at the frontier. The optional map supplies
contract inputs, and the `let` pattern names outputs such as
`let { result: value, output: instance } = step(callee);`.

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
  In a Rust or C++ object pack contract, `object_resource()` selects the
  packed object's resource. For example,
  `let { object_resource(): packed } = step(Square__click_pack_const__Shape);`
  names that instance `packed`. Other resources still use their declared
  output binders. Use the same selector in the input map of an unpack step
  to supply the packed instance.
- Omit the input map when there are no entries. An empty map is equivalent,
  and expansion uses the shorter spelling. Either form can bind a call result
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
- The retired forms `step({ ... })` and `step(callee(args), { ... })`
  are refused with this form
  ([`a_call_step_names_its_callee_not_its_call.md`](https://github.com/clicklang/click/blob/master/mdtests/a_call_step_names_its_callee_not_its_call.md)).

**Failure, checking, and tools:**

The input map and output pattern are the only sources of bindings; nothing is
searched or inferred. Expansion retains the bindings and omits empty maps.

A call publishes the callee's postconditions. It does not search memory history
to turn symbolic reads in those postconditions into extra constant equalities.
Establish the needed read equality in the proof; use `preserve(...)`
when it crosses a memory effect. Already-available equalities remain usable by
`close()` and explicit arithmetic or rewrite steps.

**Checked examples:** [`c_call_binder_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport.md), [`c_call_binder_transport_multiple_produces.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport_multiple_produces.md), [`call_result_in_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/call_result_in_condition.md), [`call_step_binder_map_on_an_uncontracted_inline_helper_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/call_step_binder_map_on_an_uncontracted_inline_helper_rejected.md)

### Named contracts with resource bindings

**Forms:** `step(Contract)` and `step(Contract, { handle: instance, ... })`.

**Specialized.** Write it to choose a named contract and map its resource
binders in one call step. Select an established named contract for the current C
call and map its resource binders. The same `let { result: value, output:
resource }` pattern binds its C value and produced resources.

A handle is a named resource clause such as `owns model: Ledger();` or
`consumes input: Dirty(p);`. The map is optional when there are no input
entries, including when the proof names produced instances in a `let` pattern.

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
- A contract that requires an input binder still needs that entry in its map.

**Failure, checking, and tools:**

Preconditions and ownership transitions use the existing call checker.
Expansion retains the bindings and omits empty maps.

**Checked examples:** [`named_contract_call_output_bindings.md`](https://github.com/clicklang/click/blob/master/mdtests/named_contract_call_output_bindings.md), [`c_step_contract_resource_count_is_model_local.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_resource_count_is_model_local.md)

### One statement obligation

**Form:** `step(...) by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
an obligation a different proof than the implicit closer. Any `step` form,
including `let` and call forms, followed by the proof of the one obligation its
primitive generates. Emitted verification conditions and call preconditions
remain obligations even when known: their ordinary `close()` proof is usually
`close()`. Arithmetic evaluation still has safety decisions that precede
obligation generation; those are not yet migrated.

The body proves that obligation at the step's pre-state, as a `have` would, and
the step then runs with it stated. The body is one tactic call, such as
`close();`, or a block.

**Failure, checking, and tools:**

Refused when the operation generates no obligation (superfluous) or more than
one; the second refusal prints every open obligation as a `requires` entry to
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
so `x == Full(a)` and `x == Full(b)` make `a == b` available to `close()`
without a stated `Full(a) == Full(b)`; see
[`constructor_injectivity_through_an_equal_value.md`](https://github.com/clicklang/click/blob/master/mdtests/constructor_injectivity_through_an_equal_value.md). Semantic fact lookup and inconsistency checking use this
indexed evidence, so `close()` can close a goal in that impossible context
without another search. The evidence belongs to the current branch and is
rebuilt when a context is restricted to selected facts; it does not equate reads across
version points where memory may have changed. Exact fact membership remains separate. See
[`model_getter_constant_conflict.md`](https://github.com/clicklang/click/blob/master/mdtests/model_getter_constant_conflict.md).

`have P;` can project an available disjunction. The solver selects a connected
stated disjunction and expands to explicit `cases`, with `close()` in each arm.
For example, `(A and X) or (B and Y)` supplies `A or B`. Every source arm must
establish the requested proposition; arm assumptions remain local.
See [`have_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/have_disjunction_projection.md)
and [`loop_exit_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_exit_disjunction_projection.md).

A simple tactic that adds a fact (`instantiate(...)`,
`apply`, `transport ... using`, and `obtain`) also closes a
proposition goal that it adds, when it is the last written step or only
`close()` or `normalize()` follows it. An added order fact closes
the goal under either form of the same claim: `0 <= e` closes the goal
`e >= 0`, and `a < b` closes `b > a`, for machine and `Integer` operands
alike. A written theorem application also closes the mirrored goal when
its checked conclusion was already stated in the context. When other written
steps follow, the goal stays open with the added fact available, so every remaining
step is still checked.

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `all { P => { ... } Q => { ... } }` | control | Expansion output | Prove each conjunct. | [Reference](#conjunctions) |
| `outcomes { returned => { ... } threw => { ... } }` | control | Specialized | Prove each returned or exceptional outcome. | [Reference](#execution-outcomes) |
| `close() using { P; ... }` | smart | Specialized | Close one goal from written premises only. | [Reference](#simplification-with-selected-premises) |
| `check_termination_local("f")` | simple | Expansion output | Establish the generated local descent classification. | [Reference](#termination-checks) |
| `check_termination_component("f", mode)` | simple | Expansion output | Classify a generated recursive component using established premises. | [Reference](#termination-checks) |
| `check_termination_callbacks()` | simple | Expansion output | Classify callback safety using established strict return premises. | [Reference](#termination-checks) |
| `close()` | smart | Core | Try the direct goal check, then search if it fails. | [Reference](#closing-a-goal) |
| `normalize()` | simple | Compatibility | Close a goal by evaluation without context. | [Reference](#context-free-normalization) |
| `normalize() using { P; ... }` | simple | Compatibility | Check normalization against written premises. | [Reference](#normalization-with-selected-premises) |
| `preserve(resource, region)` | simple | Specialized | Preserve a selected read across a separated effect. | [Reference](#preservation) |
| `rewrite(from, to)` | simple | Core | Rewrite the goal using an equality. | [Reference](#rewriting) |
| `intro()` | simple | Core | Introduce a universal binder or implication premise. | [Reference](#introducing-a-binder-or-premise) |
| `let name = intro()` | simple | Specialized | Choose the name introduced into the proof. | [Reference](#naming-an-introduced-binder) |
| `enumerate()` | simple | Expansion output | Close a constant-bounded universal from its instances. | [Reference](#finite-enumeration) |
| `contradiction(P)` | simple | Core | Close a goal from incompatible facts. | [Reference](#contradictions) |
| `contradiction()` | simple | Core | Close a goal from an established `false`. | [Reference](#contradictions) |
| `instantiate(F, value, ...)` | simple | Specialized | Instantiate an available universal fact. | [Reference](#universal-instantiation) |
| `apply(fact)` | simple | Core | Apply an established implication, proving its antecedents. | [Reference](#fact-application) |
| `apply(theorem(args))` | simple | Core | Apply a theorem and prove any open prerequisites. | [Reference](#theorem-application) |
| `unfold(function(args))` | simple | Core | Open one layer of a pure function. | [Reference](#unfolding-pure-functions) |
| `match value [ensuring { ... }] { Type::Variant(fields) => { ... } ... }` | control | Core | Prove each constructor case of an algebraic value. | [Reference](#constructor-matches) |
| `let ih = induct(value)` | simple | Core | Introduce scalar or structural induction. | [Reference](#proposition-reasoning) |
| `apply(ih(m))` | simple | Core | Apply an induction hypothesis, looking up its premises. | [Reference](#induction-hypothesis-application) |
| `have P by { ... }` | control | Core | Prove and retain a named or unnamed fact. | [Reference](#intermediate-facts) |
| `if P [ensuring { ... } then] { ... } else { ... }` | control | Core | Split a proof on a chosen proposition. | [Reference](#proposition-branches) |
| `cases { A => { ... } B => { ... } }` | control | Specialized | Prove a written collection of cases. | [Reference](#explicit-cases) |
| `with(resource) { ... }` | control | Specialized | Expose a resource body and restore it at scope exit. | [Reference](#scoped-resource-opening) |
| `witness(value, ...);` | simple | Specialized | Supply values for existential binders. | [Reference](#existential-witnesses) |
| `let name = obtain(exists (k: Type) { P });` | simple | Specialized | Name witnesses from an available existential fact. | [Reference](#obtaining-witnesses) |

`sorry()` is a dev-only proof hole, not a tactic for committed proofs: it
parses only under `click verify --allow-sorry` and closes its goal without
checking it. See [Dev-only proof hole](../cli/verify.md#dev-only-proof-hole).

When `intro` must freshen a universal binder, it uses a logical witness, a
variable kind of its own. Existential choices use witnesses too, separate from
C execution, load and binder identities. Issued witnesses remain reserved even when their
instantiated body does not mention them, so later introductions and choices
cannot reuse a live proof binding. Narrow machine binders also supply their
intrinsic bounds at introduction; these type facts need no extra `intro()`.
A written range quantifier still has its explicit range-membership guard.

`all { A => { ... } B => { ... } }` gives each conjunct a separate
proof. Each arm inherits the parent assumptions, and facts proved in an arm
stay in that arm. The `all` location owns expansion and profiling of its
nested proofs.

`by close();` is sugar for a script containing the same `close()` operation at
the same proof state, followed like every script by the implicit tail. A
`close()` written before execution has reached the function exit is refused
with the frontier it stands at; the end of a body is one `step()` of its own
(`mdtests/solve_before_exit_in_arm_names_the_frontier.md`).

Inside a `have` body, a tactic that already closed the goal (an `unfold`
whose refreshed goal is an available fact, a `transport` onto the goal, a
theorem whose conclusion is the goal) may be followed only by `close()`
or `normalize()`, which then assert the closed judgment and emit
nothing. So `unfold(f(x)); normalize();` means the same whether or not the
unfold alone closed the goal
(`mdtests/closer_after_unfold_closed_goal.md`); any other tactic after the
closure is refused by naming the tactic that closed it
(`mdtests/tactic_after_closed_goal_is_named.md`).

Scalar `induct` is available only in a pure theorem and may follow earlier
proof steps while the original theorem goal remains focused. Its hypothesis
is introduced at that step. The algebraic form is the enclosing control
tactic and therefore the only top-level tactic; its constructor arms contain
the proof steps. It is never inserted by `close()` or the implicit closer.

The algebraic hypothesis takes the theorem's complete parameter list in
declaration order. Only the inducted position is restricted: it must name a
field the current arm's pattern bound, of the datatype being inducted on.
Every other position may name any well-typed term, which is how a proof whose
recursive case changes another parameter — an accumulator, or a context frame
that grows the focused subtree — states its hypothesis. Passing only the
inducted argument remains the form for "every other parameter unchanged",
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
`instantiate` and `have` resolve their written propositions the same way.
See [`theorem_argument_arm_binding.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_arm_binding.md),
[`theorem_argument_arm_binding_algebraic.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_arm_binding_algebraic.md),
and [`theorem_argument_null_constant.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_null_constant.md).

`apply(ih(m))` checks the nonnegativity, strict decrease, and substituted
requirements for its argument. State missing premises with `have`.
Expansion preserves the application.

`enumerate` is how an explicit proof closes a finite case analysis over a
constant-bounded universal, such as a `sorted(p, 3)` postcondition: the
expanded proof spells one `have` per non-vacuous instance (typically closed by
`intro`, `instantiate(...)`, an explicit transport, and `close()`),
and `enumerate()` checks exactly those instances against the goal's own
guard-derived ranges. A goal stated as a predicate call is unfolded to the
body that binds the instances, and proof search proves nearest pairs
first so a wider span can cite its neighbours. Instances are lowered lazily: a missing instance stops `enumerate` before
visiting the rest of the numeric range, and search also stops generating
instances at its first failed proof. The finite-universal planner and its
retained certificate checker use the same lazy range order and still require
every in-range instance for success. This keeps refusal of a false frame over
a large constant range from materializing every element. Click never
instantiates by search: an in-range instance that is neither vacuous nor
written fails.

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
`pointer + index as int32` denote the same address. `close() using { ... }` checks
that the cited native bound is available and preserves the pointer stride.
A bound on the low word or a signed comparison cannot establish this unsigned
projection, and integer address equality grants no permission to access the backing
storage. Conditional normalization does not enter binder bodies.

Two displacements of one pointer by full-width unsigned indices regroup:
`(p + a) + b == p + (a + b)` for `uint64` (or `usize`) `a` and `b` at one
stride, when the sum does not wrap. The one fact read is
`to_integer(a) + to_integer(b) <= 18446744073709551615`, found by exact
lookup, and `normalize() using { ... }` can cite it. A loop that moves a
cursor forward, `v = v + cs`, carries `v == b + k` across the pass this way
([`full_width_pointer_cursor_loop.md`](https://github.com/clicklang/click/blob/master/mdtests/full_width_pointer_cursor_loop.md),
[`full_width_pointer_association.md`](https://github.com/clicklang/click/blob/master/mdtests/full_width_pointer_association.md),
[`full_width_pointer_association_requires_its_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/full_width_pointer_association_requires_its_bound.md)).

When a smart `have` needs memory permissions merely to lower its goal, its
expanded proof retains the relevant viewability and order facts through
explicit transports, rewrites, intermediate facts, or named theorem applications. A
context-free-looking result such as a normalized equality is not emitted as
bare `normalize()` if checking still needs those premises to interpret an
indexed load. A `close() using` equality may be selected through a bounded chain
of exact equality facts whose intermediate load variables are kernel-internal
names for the same user-level loads. When frame evidence is needed to relate an
earlier load origin to the current one, the expanded proof first establishes the
current surface form with an explicit `transport`; simple `rewrite` checking
never searches for an equivalent equality. Expansion and audit verify the
complete rewritten surface proof through the ordinary entry point.

### Conjunctions

**Form:** `all { P => { ... } Q => { ... } }`

Write one labeled arm per conjunct in any order. For `P and (Q and R)`, a
single block may contain three arms. Repeated conjuncts take separate arms.
Identically labeled arms are used in written order.
An arm can also name a whole conjunct that is itself a conjunction, for
example when its proof changes the goal before splitting it.

Each proof starts with the parent assumptions. Facts established in one arm
are local to that arm. An absent, extra, or unfinished arm fails. An ordinary conjunction can still be closed by `close()`.

Expansion writes a flat list using the retained child goals or by raising
their kernel propositions from the names in scope.

**Checked examples:** [Conjunction goals](https://github.com/clicklang/click/blob/master/mdtests/proof_both_and.md)

### Execution outcomes

**Form:** `outcomes { returned[(value)] => { ... } threw[(error)] => { ... } }`

**Specialized.** Write it at a C++ call that may throw, when the two outcomes
need different proofs; the implicit tail splits them for you. At a maybe-throwing
call, `outcomes` executes the call and starts each arm at its checked successor. Inside a `try`/`catch (int name)` the `threw`
arm follows the caught exceptional edge into the handler.

Outside any `try` the `threw` arm ends at function exit with that throw, while
the `returned` arm continues with the rest of the function and may hold the next
call's own nested `outcomes`. The implicit tail splits every maybe-throwing call this
way, inside a C `if` arm as well as at top level, and expansion writes the split
it took.

Write `returned(value)` to name the checked value of a call whose result the
program uses. Write `threw(error)` to name the thrown payload. Each name is a
proof binding scoped to its arm. At function exit, the same syntax selects
the call edge already recorded on the path and binds the same call payload.
For example, a call's returned value still names that value after the caller
transforms it, and a caught exception names the original thrown value even
if the caller returns normally. An arm without a name can ignore its payload.

**Failure, checking, and tools:**

The checked execution must establish exactly one edge of each kind. Each arm has
its own outcome goal and must close it; neither arm can use the other's facts or
state. Expansion preserves both certificates.

**Checked examples:** [`cpp_import.rs`](https://github.com/clicklang/click/blob/master/tests/cpp_import.rs), [`outcomes_routes_a_throw_that_leaves_the_function.md`](https://github.com/clicklang/click/blob/master/mdtests/outcomes_routes_a_throw_that_leaves_the_function.md), [`outcomes_payload_bindings.md`](https://github.com/clicklang/click/blob/master/mdtests/outcomes_payload_bindings.md)

### Simplification

**Search after the direct check in `close()`.**

`close()` closes one goal and runs no C. The parser refuses a written `auto();`, naming
`close();` for it and the omitted proof for `by auto();`. `by close();` restates what an omitted proof of a
`have` or a pure theorem's `ensures` does, but it is accepted: it marks a place
to write a different tactic later.

**Core. On a proposition goal, search ambient pure facts and bounded rules for
a simple proof. A signed `int32` goal over variables is tried with one
ordinary arithmetic proof from the indexed bounds reachable from those variables (a
bound `i < n` leads on to `n`'s bounds, up to eight variables), the same way in
a pure theorem, before execution, mid-function, in a `branch` arm, and at
function exit; a negated branch condition counts as a bound. Constant bounds on
the goal variables are tried before following relational bounds, so earlier
postconditions on those variables do not exhaust the arithmetic premise limit.

An equality of two `uint32`, `int64` or `uint64` values closes from the two
opposite order facts on its operands, `a <= b` and `b <= a` in any form
(`a >= b`, `not (a < b)`), looked up exactly and cited by one `close()
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
has its opposite among the facts closes by `contradiction` once `close()`
introduces it, whichever form the facts state the opposite in (`x > 100`
for `x <= 100` false), so `a and b implies c` closes where the curried
`a implies b implies c` does
([`solve_refutes_a_conjunct_of_an_antecedent.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_refutes_a_conjunct_of_an_antecedent.md),
[`solve_keeps_a_conjunct_antecedent_that_holds.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_keeps_a_conjunct_antecedent_that_holds.md)).

A goal that is one conjunct of an implication's consequent, `c == 2` from
`a != 0` and `a != 0 implies (b == 1 and c == 2)`, is closed once the
antecedent is an exact available fact: unit propagation publishes the whole
conclusion, and expansion can close the selected conjunct with `close()`.
When the guard needs proving first, expansion may retain an explicit
`apply(fact)`
([`solve_closes_a_conjunct_of_a_discharged_consequent.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_closes_a_conjunct_of_a_discharged_consequent.md)).

A comparison held only under a definedness guard (`defined(e) implies a == b`,
as a call postcondition over partial arithmetic lowers) whose consequent names a
goal operand is used once a nested `close()` proves the guard: the closer applies
the implication with explicit evidence and rewrites the goal with an equality
or closes from the new fact.

An `int32` or `int64` definedness goal `defined(a + b)` or `defined(a - b)`
selects the constant order and equality facts of that width indexed under each
operand. It states intrinsic operand ranges and proves both ordinary bounds on
the exact result, using local interval normalization or Integer laws. Expansion
retains those `have` proofs and closes the domain with `close()`; it emits no
signed-definedness ordinary arithmetic proof.

A recursive specification function applied to a known constructor is
evaluated: `close()` unfolds it, then keeps unfolding the recursive calls the
definition exposes while their arguments select one arm, rewriting an argument
by a constructor equation (a supplied premise or a connected fact such as
`u == Tree::Node(..)`) when that exposes one, for at most eight checked steps.

A recursive call whose arguments are constants, such as
`output_from(lit, 0u64, 13)` that a postcondition names, is evaluated one
level at a time instead. Each level is the arm of the definition that its
constant `if` guards select, with the next call's constant arguments
evaluated; a guard may compare a string literal's byte at a constant index,
which is a constant since the literal is read-only. `close()` proves one
`have` for the call's value, and inside it one `have` per level, `call ==
arm`, by `unfold` and `close()`. Only the
value joins the proof, so the work grows linearly with the depth, at most
1024 levels. A call a fact names inside `at(point, ...)`, as a postcondition
names it at the call's entry, is evaluated at that point, with
`unfold(at(point, call))`. Expansion writes the `have`s
(`mdtests/a_recursive_byte_function_evaluates_automatically.md`,
`mdtests/a_long_recursion_over_constants_is_evaluated_one_level_at_a_time.md`).
A bottom-up proof, one `have` per call by `unfold` and `close()`, states the
same levels by hand
(`mdtests/a_recursive_byte_function_evaluates_a_string_literal.md`).
An argument nothing fixes stays folded
([`solve_evaluates_a_recursive_function_over_known_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_evaluates_a_recursive_function_over_known_constructors.md),
[`solve_does_not_evaluate_a_recursive_function_past_an_unknown_argument.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_evaluate_a_recursive_function_past_an_unknown_argument.md)).

An existential `exists v { x == C(.., v, ..) }` whose `x` a fact fixes to a
constructor of the same variant, `x == C(.., t, ..)`, takes `t` as its witness:
`close()` writes `witness(t)` and closes the instance. A constant payload is
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
the operand equal to the sum without it by `close()`, then the restated goal from
its bounds
([`solve_defined_count_after_a_zero_summand.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_defined_count_after_a_zero_summand.md)).

When the goal also carries an operand's own definedness, such as a field read
through a resource, `close()` proves `defined(operand)` as a `have`, separately
from the exact-result bounds
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
where `r == 0`, is closed by selecting the implication and expanding to
`apply(fact)`, with the goal's `at(...)` points as written.

A guarded universal goal `forall k { G implies A }` closes from an available
`forall k { G implies A and B }` with the same binder and guards, selected by one
indexed lookup of the conjuncts guarded universals conclude. The proof is `intro()`
for the binder and each guard, `instantiate` at the introduced binder, and
`close()`, so `memset`'s `defined(..) and` value postcondition supplies
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

**Form:** `close() using { P; ... }`

**Specialized.** Write it when `close()` picks the wrong premises or searches too
long, to restrict it to the named facts. On a proposition goal, including a
contract claim after function exit, search using exactly the listed proposition
facts. A preceding `have` is available on each outcome where it was proved;
grouped proposition and ownership claims retain their checked resource
transition.

A listed guarded equality whose definedness guard is not listed has the guard
proved first, from the other listed facts when they suffice, and is then used as
its consequent. An `int32` or `int64` definedness goal uses the listed operand
bounds and intrinsic type ranges to prove the two exact-result bounds through
ordinary `close()` leaves and Integer laws. For an Integer goal observing a machine sum or difference,
listed bounds and the machine type's range can establish the in-range
identity, such as `to_integer(x + 1) == to_integer(x) + 1`. Expansion writes
the range proofs and a `close()` identity step. An
unsigned operation is used this way only when those bounds prove it does not wrap.

Available verified theorems are reasoning rules, not extra hypotheses. If the
existing strategies miss, `close() using` searches for one theorem application
whose conclusion structurally matches the goal. Every value argument must be
determined by that conclusion; generic type arguments are inferred by ordinary
application checking. The solver checks the instantiated requirements and argument guards against
the listed facts before choosing the application.
An unconditional theorem can therefore close `close() using {}`.

Conclusion matching treats reversed `==` and `!=` operands and mirrored
orders (`a > b` / `b < a`, `a >= b` / `b <= a`) as the same comparison.
Both symmetric orientations remain available when theorem prerequisites
must disambiguate the inferred arguments. Repeated parameters retain one
consistent assignment across the whole conclusion. This adds no conversion
between strict and non-strict orders or between negated and complementary
float comparisons, where NaNs matter. Expansion still cites the original
theorem with its inferred arguments.

<!-- verified-example: mdtests/solve_using_equivalent_comparisons.md -->
```click
function fixed(x: Integer) -> Integer { 7 }

theorem lower_bound(x: Integer) {
    requires 0 <= x;
    ensures fixed(x) >= 7 by { unfold(fixed(x)); close(); }
}

theorem equality(x: Integer) {
    requires 0 <= x;
    ensures fixed(x) == 7 by { unfold(fixed(x)); close(); }
}

theorem test(value: Integer) {
    requires 0 <= value;
    ensures 7 <= fixed(value) by { close() using { 0 <= value; }; }
    ensures 7 == fixed(value) by { close() using { 0 <= value; }; }
}
```

This first slice supports binder-free structural matching of comparisons,
predicate calls, definedness, and proposition expressions, including ordinary
arithmetic and function-call operands. It does not invent arguments absent
from the conclusion, match modulo arbitrary equality, or chain applications.
Discovery uses an index of conclusion shapes and function/predicate symbols,
runs under the normal solve work budget, and expands to
`apply(theorem(args))` when its obligations can be checked from the facts in
scope. Expansion retains separate proofs for open obligations.

<!-- verified-example: mdtests/solve_using_discovers_one_theorem.md -->
```click
function shifted(x: Integer) -> Integer { x + 7 }

theorem shifted_bound(x: Integer) {
    requires 0 <= x;
    ensures 7 <= shifted(x) by { unfold(shifted(x)); close(); }
}

theorem use_bound(value: Integer) {
    requires 0 <= value;
    ensures 7 <= shifted(value) by {
        close() using { 0 <= value; };
    }
}
```

**Failure, checking, and tools:**

A missing fact or missing simple rule fails. Click uses the generated explicit
proof rather than repeating search; expansion emits the named steps or reports
the rule gap, and profiling reports the restricted site.

**Checked examples:** [`condition_search_explicit_decomposition.md`](https://github.com/clicklang/click/blob/master/mdtests/condition_search_explicit_decomposition.md)

### Closing a goal

**Form:** `close()`

`close()` first checks whether the current goal follows directly from the
available facts. If the check misses, ordinary verification runs bounded
search. Checked-only verification reports
the direct-check failure at the tactic. `click expand` emits the checked
steps selected by either path, spelling direct goal closures `close()`.

<!-- verified-example: mdtests/close_tactic.md -->
```click
theorem closes_by_search(x: int32) {
    ensures x == 0 implies x == 0 by close();
}
```

### Available facts

The direct check in `close()` also handles computational leaves after a
rewrite or unfold and inside logical proofs. Use
`click verify --checked-only` to require replay without search.

**Accepts** a goal that is available, where an atomic proposition is
available when one of these holds:

- It is a fact, or a leaf conjunct of a fact. An implication or quantified
  goal must be such a fact up to renaming of its bound variables.
- It is a viewability goal for an empty byte span or for a concrete span
  within the exact block recorded in the goal's memory state. A nonempty
  span uses the written base identity, offset, and span size.
- The completed execution path diverges and the goal is a return
  postcondition.
- It is a typed read-definedness goal whose memory state holds a compatible
  cell or one unambiguous live slot of the requested type at the exact
  address. It also accepts the whole read of a declared local `uint32` when
  all four bytes are recorded initialized or have exact `uint8` definedness
  facts in the same state. The unsigned word's declared type makes every
  initialized bit pattern valid. This establishes read definedness while
  execution still checks memory permission.
- It checks containment of constant byte intervals with the same address
  origin, including intervals written at different element widths.
- It separates a complete recorded effect footprint from the named
  resource. For each recorded member, the checker tests intrinsic
  separation or looks up the exact member separation. Two ranges that meet
  at a byte boundary are separate when the signed endpoints of the leading
  range are ordered. A sequence with multiple effects needs individually
  checked steps.
- It is a separation of memory ranges on distinct static objects or
  distinct automatic objects, or between an automatic object and storage
  incoming to the function. Two ranges on the same symbolic base can also
  be separate by their exact constant byte intervals. Forming the ranges
  still carries the ordinary range obligations.
- It follows by exact Boolean unit propagation. Admitting `A or B` and
  `not A` makes `B` available; admitting `A implies B` and `A` makes `B`
  available. Either admission order works, and consequences propagate through
  chains and conjunctive guards. Matching preserves proposition syntax, types,
  and memory states; it does not search for equivalent guards. Each clause
  occurrence is processed at most once per proof-context lineage, and
  `close()` reads the resulting ordinary fact indexes. See
  [`exact_proposition_propagation.md`](https://github.com/clicklang/click/blob/master/mdtests/exact_proposition_propagation.md).
- It is another spelling of an available order claim, in every order family
  (C machine integers and `Integer`): `0 <= x` for `x >= 0`, and `not(y <= x)`,
  `y > x` and `x < y` for one another. `x != y`, `not(x == y)`, and
  `y != x` are one claim.
- A float comparison has its operands reversed with the matching relation:
  `a > b` / `b < a`, `a >= b` / `b <= a`, and reversed `==` or `!=`.
  Width and truth polarity stay fixed; negated float orders are not treated
  as complementary orders, since NaNs would invalidate that rule.
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
order comparisons close when their symbolic terms cancel. Identical calls,
reads, folds, and symbolic matches may cancel as opaque operands. An equality
with an `int32` union member can also use the typed value stored at its exact
address and memory state. A by-value copy can store the source read itself
as that value. The check uses one typed cell lookup per operand. A native
signed `int32` comparison against a literal can also use the literal
stored at the read's exact typed cell.

A machine-valued range fold whose step returns its accumulator equals its
initial value. This check reads only the accumulator binding and the initial
value.

After an explicit `unfold`, `close()` can check values and bounds of machine
expressions such as decimal lengths and their padded lengths. It follows a
decided guard and otherwise bounds both arms. Its arithmetic uses only the
operands in the goal, with a bounded walk and checked machine ranges.

A match on a written constructor can close an equality when its selected arm
builds a constructor from bound fields, literal fields, or captured variables.
Literals and variables can be machine integers, `Integer`s, or `Bool`s.
Algebraic result fields can also be constructors that contain these values.
A constructor passed into a pattern binder can contain literals, variables,
and nested constructors. The check reads those variables in the scope where
the constructor was written. It follows nested matches on written constructors
or constructors held by earlier pattern binders. A selected arm can return
a bound or captured algebraic value directly. An equality can compare
the selected results of two matches, with each side using its own bindings.
Within a selected arm, a literal guard or a Boolean pattern binder holding a
literal can select an `if` branch. Machine fields retain their exact width and
signedness.

Two values of the same constructor are unequal if a corresponding field
holds a different machine-integer literal of the same type. The check
visits only the immediate fields and uses their literal values.

Direct computation also recognizes the neutral bitwise identities `0 & x == 0`
and `0 | x == x` at a native word's own format, in either operand order. A bitwise
OR is unequal to zero when either operand is a same-width nonzero literal. The
rule also applies to the exact `Integer` observation of that word. Intrinsic
alignment of a null, heap, global or static address reads only that address's
block registration and constant byte offset. It does not search alignment facts
or infer alignment for a symbolic offset.

For a written alignment goal, `close()` may also look up the base's recorded
alignment by coordinate. A constant byte displacement or a symbolic index at
a stride divisible by the requested alignment preserves the corresponding
residue. The check probes only the base and the supported alignment strengths.

The same fixed local check accepts intrinsic machine type ranges and
constant-divisor quotient, remainder, and right-shift bounds. This includes
`x % d < d` and its exact Integer reading for a positive machine literal `d`.
An unsigned `x % d` is at most `x` when the exact divisor is known nonzero.
Signed quotient and remainder bounds against zero use the named operand
signs and the divisor's nonzero guard. Machine operations also require
evidence that excludes the signed minimum divided by `-1` when the signs
alone leave that pair possible. A signed product's exact Integer bound at its
machine minimum or maximum uses the two operand signs and the corresponding
quotient guard when needed. The written product and endpoint name the guards
for exact lookup.
A full-width unsigned index agrees with its signed low word when both use
the same base and stride and the full-width index is at most `INT32_MAX`.
`close()` checks this bound on the full-width index itself. See
[`uint64_int32_owned_index_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_owned_index_alias.md) for a store through the full-width index and a read through the signed index.
A written machine `+`, `-`, or `*` observation equals its exact Integer expression when
both exact-result range bounds are available. An integral cast or `to_T(z)`
observation equals its operand when the destination-range bounds are available.
Each check reads the named operands and at most two exact bound keys; it does
not search for an interval or derive missing bounds.

For a valid literal shift count, a left-shift observation equals multiplication
by its power of two when the exact result is in range; signed shifts also
require a nonnegative source. A signed OR or XOR of two nonnegative
operands excludes `-1`. A word OR with a nonzero operand excludes zero.
A bitwise-and with a
nonnegative literal mask is between zero and the mask, and is at most a
nonnegative source. For
unsigned words, this range also supports comparisons of compound expressions.
For example, `close()` can prove `((y & 7u32) + 1u32) as uint32 != 0u32`
because the addition's range is `[1, 8]` and fits the word.

For a 32- or 64-bit shift count, `close()` can remove the mask `width - 1`
when the count is known in range. It also checks the equality of the signed
and unsigned right shifts of the positive signed maximum at the same in-range
count. A constant right shift of a zero-extended unsigned byte or halfword
has a range computed from its source width and count, including after a
signed widening of the result.
For a positive literal left operand, a count bound below the point where
the result would reach the sign bit establishes that the shift fits.

A root conditional equals its selected arm when its written guard is available.
A root Integer or machine conditional with identical arms equals that shared
arm without a guard premise.
Shared native comparison guards retain their operand DAGs; other shared
compound guards require explicit logical steps rather than exporting a guard
tree. Missing guards and unsupported forms are refused.

Nested `int32` conditionals can compute their selected value when each
selected guard is a constant, a reflexive equality, or an equality of
literals. This also applies to the conditionals left by a checked
constructor rewrite.

A conjunction goal closes when every conjunct does, and a disjunction goal
when one disjunct does, using available facts or these computations recursively.
An implication goal `A implies B`, alone or as a conjunct, closes when `B` is
an available fact, with one lookup of `B` and no introduction
(`mdtests/known_closes_an_implication_whose_consequent_is_known.md`). This
closes a guarded requirement such as the domain owed by the right side of
`and` once that domain is known.
A negated conjunction closes when direct computation refutes one conjunct.
A negated disjunction closes when it refutes every disjunct. For example,
different literal elements can prove finite-sequence disequality or
non-membership. Computational truths inside an implication or quantifier
still require the ordinary introduction or witness steps. An implication or quantified goal
already held as a fact retains its existing exact-lookup behavior.

**Outside it**, with what to write instead:

- A consequent of an available implication: `have Q;` or apply the implication
  with `apply(fact)`.
- A reordered disjunction fact (`y > 0 or x < y` from `x < y or y > 0`):
  `have y > 0 or x < y;`, which expands to `cases`, then `close()`.
- A weaker or derived bound, such as `x <= y` from `x < y`: `close()
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

For exactly named, independently held resources, `close()` applies the
live partition rule: an owned unit is separate from another owned unit or a
view. Two views alone do not establish separation. The rule uses exact resource
lookups; it does not enumerate aliases or compositions, and supported cached
projections do not count as independent entries. It also applies to separation
leaves in a conjunction. Constant disjoint intervals of the same base can
instead be proved by `normalize()`.

An explicit `have separate(...)` can use the live ownership partition
immediately after `unfold`, including fixed-size fields fully contained in
different owned objects; it checks complete byte coverage and grants no new
ownership. It also selects two different resources of any kind that the
state owns exactly as written, for example a just-folded resource instance
and a cell owned beside it. `split()`, `left()` and `right()` were folded into this tactic and
are refused with that advice.

Lookup also accepts certified identity of a resource separation. It performs
no function unfolding, implication search, or fact transport across effects.
Exact propagated consequences are already available facts. Expansion leaves
this step unchanged, and profiling charges one simple leaf.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`known_computes_fast_leaves.md`](https://github.com/clicklang/click/blob/master/mdtests/known_computes_fast_leaves.md), [`known_closes_an_evaluated_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/known_closes_an_evaluated_goal.md), [`simple_statement_step_explicit_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_explicit_transport.md)

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
  negations, and constant-coefficient products of exact `Integer` terms compares their affine forms over the
  integers, with no modulus: when every term cancels, the constant difference
  decides it. `1 + to_integer(x) == to_integer(x) + 1`,
  `to_integer(x) - to_integer(x) == 0`, `a + b == b + a` for `Integer`
  parameters, `to_integer(x) + 1 != to_integer(x)`, and
  `to_integer(x) + 1 > to_integer(x)` are true. C machine order claims are not
  compared this way, since `x + 1 > x` is false at a type's maximum.

For explicit Integer normalization, `2 * x == x + x`,
`3 * (x - y) == 3 * x - 3 * y`, and `(2 + 3) * x == 5 * x` also hold.
Products also normalize association and factor order within each monomial.
One explicit symbolic distribution, `(a + b) * c == a * c + b * c`
(or subtraction, or distribution on the other side), is a local primitive
with opaque operands. Full polynomial expansion is search: `close()` writes
individual distribution equalities and rewrites before normalization. Calls,
reads, and folds remain opaque. Checking reads no facts. The computational `close()` leaf
retains its narrower sum/difference rules. C machine multiplication also
remains opaque; these exact Integer identities introduce no machine overflow
or definedness facts.

**Outside it**, with what to write instead:

- A top-level `and`, `or`, implication, or quantifier: use `all`, prove one
  disjunct with `have` and close with `close()`, or `intro`.
- A goal that needs a fact, including a premise of the theorem: use
  `normalize() using { P; ... }`, `rewrite`, or `close()`.
- A pure function call: `unfold` it first; `normalize` leaves calls symbolic.
- Distributing a symbolic product, such as `(x + y) * z == x * z + y * z`;
  an order claim between C machine sums, such as `x + 1 > x`; or an `Integer` order claim whose terms
  do not cancel, such as `to_integer(x) < to_integer(x) + to_integer(y)`: use
  `close() using { ... }` or an ordinary arithmetic proof.

**Failure, checking, and tools:**

A refusal prints the goal after substitution. Click runs the deterministic
leaf check; expansion is unchanged, and profiling charges the normalized
expression. Smart tactics retain the corresponding `all`, disjunct proof and
`close()`, or `intro` proof.

Intrinsic Integer bounds on a machine quotient, right shift, or remainder
by a positive constant also normalize without facts, in the bound's written
shape: `c * to_integer(x / c) <= to_integer(x)` for unsigned division, its
upper bound with slack `c - 1`, and the corresponding signed slack bounds.
The divisor and shift count retain the native operation's type and domain.
No operand history or ambient facts are read.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md)

### Normalization with selected premises

**Form:** `normalize() using { P; ... }`

This compatibility form checks a goal under its named premises. Expansion
retains written calls. The tactic decides conditions in the goal from the cited
premises and the equality graph, then applies `normalize()`'s check (see
[Context-free normalization](#context-free-normalization)) to the result.

For a signed `int32` order goal, the cited comparisons can form a chain in
list order from the goal's lower endpoint to its upper endpoint. A strict
goal needs at least one strict link. Replay checks the listed links directly.

A true `float` or `double` comparison against a literal can cite one stronger
bound. Exact widening from `float` to `double` widens the endpoint and preserves
the direction. Narrowing from `double` to `float` rounds the endpoint and
gives a non-strict bound in the original direction. Unary float negation negates the endpoint and reverses the
direction. Adding or subtracting a finite literal, subtracting from a finite
literal, and multiplying or dividing by a finite nonzero literal transform
and round the endpoint at the same width. Subtraction from a literal and
multiplication or division by a negative literal reverse the direction.
The rounded endpoint gives a non-strict bound because
distinct inputs can round to the same result. An unchanged or exact endpoint
requires a strict premise for a strict goal with that endpoint. A negated comparison can hold for NaN and cannot
supply an ordered bound. A sum or difference of two float operands can
cite one ordered bound per operand with finite literal endpoints. A sum
uses two bounds in the goal's direction. For a difference the right
operand's bound points in the opposite direction. The rule combines and
rounds the endpoints at the operation's width.
For a finite nonzero literal divided by an operand bounded away from zero,
cite the divisor's endpoint nearest zero. The two quotient bounds are zero
and the rounded quotient at that endpoint. A strict bound can use the next
representable value on its admitted side, such as the smallest positive
`float` for `x > 0`.
For a product or quotient with two finite operand ranges, cite the lower
and upper endpoints of both ranges. The rule checks the four corners at
the operation's width. A quotient's divisor range must exclude zero.
A square can cite just the two endpoints of its operand's range. Its
lower bound is zero if that range crosses zero.
A product's lower bound can instead cite two strictly positive lower
endpoints. Multiplication by a literal signed zero can cite a finite
operand or its two finite bounds. `close()` accepts the exact
`isfinite` premise for the zero product.
`close()` can select these float bounds and expand to `normalize() using`
with the selected premises.


For two negative signed operands, `x < 0`, `y < 0`, and
`x >= MAX / y` bound their product by `MAX`. This guard permits
`y == -1` because `MAX / -1` is defined. A lower product bound
using `MIN / y` with a negative divisor still needs `y < -1`.

For an unsigned left shift of one, citing the count bound proves the result
is nonzero. For example, `normalize() using { d < 32u32; }` proves
`(1u32 << d) != 0u32`. This also discharges the divisor obligation for
C division and remainder.

An in-range operation or cast identity also accepts exactly two ordered
Integer bounds on its exact result: the lower bound, then the upper bound.
Both must lie within the operation or destination format. A bound on one
Integer product accepts exactly four bounds, the lower and upper range of
the left operand, then those of the right operand; all four corner products
must imply the stated bound. These are fixed intrinsic checks over the
written goal and citations. They do not plan arithmetic or construct an
ordinary arithmetic proof. See
[`integer_machine_bridge_normalization.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_machine_bridge_normalization.md)
and its wrapping and false-corner refusal controls.

The specialized selected rules also accept exact Integer division/remainder
bounds from four ordered constant endpoints, multiplication order from an
ordered pair and its factor's sign, quotient bounds from a scaled bound and
a positive divisor, and a constant-divisor quotient shift from the two
nonnegative operands. Pointer translation names its equality first and scalar
bounds after it; tagged-word rules name their word equality first (when used)
and then the alignment facts. One finite classification proves the matching
reflexive IEEE comparison. These are fixed local rules over explicit inputs;
none selects premises or expands a polynomial.

For a reflexive `float` or `double` comparison, `close()` expands to
`close()` when the exact `isfinite(x)` fact is available for the common
operand. Restricted `close() using` must select that fact. For example,
`isfinite(x)` establishes `x == x`, `x <= x` and `not(x < x)`. An ordered
bound on an exact float widening or sign negation also closes with
`close()` from the corresponding input comparison at the same endpoint.
Negation reverses the order and flips the endpoint's sign. The widening
check requires the endpoint to be exactly representable in the input width.
For a weaker result bound, `close()` records the transported comparison in
a `have` and applies the corresponding `click::float_order` transitivity law.

For supported native unsigned address words, `close()` emits ordinary `have`
goals, `apply(click::integer::...)`, rewrites, and `close()`: alignment
weakening, scalar element offsets, low-tag projections and high-mask recovery
name their local laws and retain the unsigned width explicitly. Remaining
legacy forms still use the compatibility normalization path.

**Accepts** a goal that `normalize()` accepts after this reduction, when every
cited premise is accepted:

- A premise is accepted when it is available in the sense of `close()`'s
  atomic rules, or in its other polarity or direction, or holds without facts
  (`0 <= 0`), and it is a single condition or its negation: a comparison, an
  equality including an algebraic one, or its `not`. The list may be empty.
- Each condition in the goal, at any depth outside binders, including the goal
  itself, a conditional-expression guard, and a condition inside a
  pure-function argument, becomes `true` or `false` when a cited premise
  states it in any form: as written, at the other polarity (`x >= y` is
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
- A signed `int32` operation's constant interval follows from the cited
  endpoints of its opaque operands: addition, subtraction, multiplication,
  constant remainder and shifts, a nonnegative constant bit mask, and an
  in-range cast. Exact addition/subtraction over bounded machine observations
  uses the same endpoint calculation without machine wrapping. Nested
  operations need explicit intermediate bounds. A bounded nonnegative
  remainder also transports through a stated constant addition when its
  translated interval crosses no divisor boundary. No operand interval is
  recursively searched. A separately stated exact domain can intersect an
  operation's result with its signed type range
  ([`signed_interval_normalization.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_interval_normalization.md)).
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
  ([`element_offsets_from_exact_index_sum.md`](https://github.com/clicklang/click/blob/master/mdtests/element_offsets_from_exact_index_sum.md),
  [`normalize_using_refuses_a_wrapping_index_sum_for_an_address.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_refuses_a_wrapping_index_sum_for_an_address.md)).
- For a top-level read equality of any width, a pointer read equality, or a
  pointer-offset equality, the cited conditions can justify the read's
  recorded stored value or the offsets' equality directly, and for
  `defined(...)` of a read, that a store wrote its bytes; see the paragraph
  below.

**Outside it**, with what to write instead:

- A premise that is a conjunction, disjunction, implication, or quantifier:
  `have` the single condition and cite it. Two premises stating opposite
  values of one condition are refused as inconsistent.
- A goal that needs a cited equality's value substituted into a term, such as
  `x * 2 < 15` from `x == 7`: `rewrite(x, 7)` then `normalize()`
  ([`normalize_using_decides_conditions_without_substituting.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_decides_conditions_without_substituting.md)).
- A goal between two symbolic terms that follows from a cited premise without
  being one of its forms, such as `x <= y` from `x < y`:
  `close() using`.
- An unlisted ambient order condition, or an ambient `Integer` or algebraic
  equality: cite it.
- A top-level conjunction, disjunction, or implication remaining after
  reduction: `all`, a disjunct `have`, or `intro`, as for `normalize()`.
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

**Checked examples:** [`normalize_using.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using.md), [`normalize_using_graph_conditions.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_graph_conditions.md), [`normalize_using_rejects_ambient.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_rejects_ambient.md), [`normalize_using_decides_conditions_without_substituting.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_decides_conditions_without_substituting.md), [`uint64_int32_exact_index_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_exact_index_alias.md), [`uint64_int32_low_word_is_not_address_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_low_word_is_not_address_equality.md)

### Arithmetic search

**Form:** `close() using {}`. The parser refuses the removed form
`arithmetic()` and names `close() using {}`.

**Specialized.** Write it only for a bound that follows from the goal's own
terms, such as `(x & 255) <= 255`; it reads no fact. `close() using {}` tries
the engine this section describes after its other closers, over no premises.
The engine plans a bounded proof of the current comparison or equality over
signed `int32` values or mathematical `Integer` expressions. Signed interval
plans expand into ordinary `have` steps, normalization, and Integer law
applications, with explicit operation domains and observation identities.

The family is decided by the goal's own checked terms, never guessed from its
written form, and the two never coerce into each other. For `int32`, affine terms
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
precondition. Expansion retains the ordinary checked operations selected by the
plan. All supported arithmetic families expand to ordinary proof steps.

**Checked examples:** [`pure_arithmetic_affine.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_affine.md), [`pure_arithmetic_bounded_operations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_bounded_operations.md), [`arithmetic_on_an_unfold_refreshed_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_on_an_unfold_refreshed_goal.md)

### Arithmetic with selected premises

**Form:** `close() using { P; ... }`. The parser refuses the removed form
`arithmetic() using { P; ... }` and names `close() using { P; ... }`.

**Specialized.** Write it when `close()` misses an integer bound or equality,
listing the premises the bound follows from. `close() using` tries the
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
overflow. A goal written with `>` or `>=` is read from the other side, so a bound
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
value the goal and listed premises observe, stated over the written operand,
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
`close()`, a listed `not left < right` is read as `right <= left` and a
listed `right > left` as `left < right`, each value written beside a sum or
difference has its type's range stated by `close()` (so `i -
1` is defined under `0 < i`), each sum and difference in the premises and the
goal is shown to stay in range from the facts before it, by both constant
bounds of its exact value, and observed by a `close()` identity step reading those bounds, the Integer claim is proved in the `Integer`
family, and `close()` concludes the goal. A listed premise the proof does
not hold is refused as an unavailable exact premise.

An equality goal takes its type from a listed order premise or a typed literal,
and is read this way only when both sides are sums and differences of plain
operands; an equality over a product, a shift or a mask is left to the other
families. An unsigned sum must not exceed the type; a signed one is defined
once both Integer bounds of its exact value are facts, which together are its
definedness fact, so `close()` states it; a premise over a signed sum is
carried only once that sum is defined.

Expansion writes those steps as ordinary `have`, `apply(...)`, and
normalization steps with explicit premises.

A disequality goal `a != b` (or `not (a == b)`) over machine or `Integer`
operands, which no certificate family reads directly, is proved by refuting
`a == b`. In the equal arm of a proof `if`, arithmetic proves `false` from
the listed premises and the equality. The other arm has the disequality as a
fact. `k < j` gives `k != j`
([`arithmetic_proves_a_disequality_by_refuting_its_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_proves_a_disequality_by_refuting_its_equality.md));
`k <= j` does not, and the refusal is the one for the `false` goal
([`a_disequality_its_premises_allow_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/a_disequality_its_premises_allow_is_refused.md)).
`close()` proves `a < b`, or else `b < a`, by selected-premise arithmetic,
which a linear refutation of `a == b` always leaves, and refutes the equality
from it. Expansion writes that `have` and the two arms of the proof `if`.

Arithmetic reads no disequality premise, so a disequality goal that only
another disequality gives is proved by cases. When every other strategy
misses, `close()` splits on `a == b` and, in that arm, proves `p == q` for an
available `p != q` connected to the goal (at most four, in turn), which
`close()` closes against the stated fact; the other arm holds the goal.
This carries the Integer fact `m - 1 != 0` to the `int32` word fact
`((m - 1) as int32) != 0` where the facts keep `m - 1` in range, and back.
It refuses where the word may wrap: `u + 1 != 0` over a `uint32` `u` does not
give `((u + 1) as uint32) != 0`
([`a_store_index_fact_may_be_the_integer_or_the_word.md`](https://github.com/clicklang/click/blob/master/mdtests/a_store_index_fact_may_be_the_integer_or_the_word.md),
[`an_integer_disequality_does_not_give_a_wrapping_word_one.md`](https://github.com/clicklang/click/blob/master/mdtests/an_integer_disequality_does_not_give_a_wrapping_word_one.md)).
Expansion writes the proof `if`, the `have p == q` with its certificate, and
the two `close()` steps.

After that, a pointer disequality between two element addresses of one
base, `&q[j] != &q[0]`, whose indices have one width and format (`int32`, or
64-bit of one signedness), is reduced to its indices: `close()` states
`have j != 0` (written from the index words, as the store search writes its
fact: `((m - 1) as int32) != 0`, `j != 0u64`), proves it by `close()`, and
closes the goal with
`apply(click::separation::distinct_elements(q, j, 0))`.
Expansion writes that `have` and the `apply`. Where the indices may be equal
the nested `close()` misses and the goal's ordinary refusal stands
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

**Form:** `preserve(resource, region);`

A simple tactic for read equality, read definedness, or range viewability.
Select the resource and the recorded region across which to preserve it. Use
`have` to establish the exact fact `separate(region.footprint, resource)` in
either order. For evidence at a saved snapshot, write
`preserve(at(mark, resource), region)`. Here `at(mark, resource)` is an ordinary
resource descriptor evaluated at the saved snapshot, just as in `separate` or
`contains`. Parentheses only group: `(at(mark, resource))` has the same meaning.
The tactic applies one primitive using the recorded region endpoints and exact
facts. For equality goals, it constructs equality of the selected read at the
exit and entry, in that order. The goal selects the read type or named-resource
field and must match the constructed equality.

For `defined(read)`, the separated resource must be the complete typed cell.
The tactic looks up the exact `defined(read)` fact at the footprint's entry
and constructs it at the exit. The footprint supplies both points; the
separated cell supplies the address. Missing old definedness is a local refusal,
not a request to search memory history. This rule preserves definedness; it
does not establish initialization from ownership or value equality alone.

For a `viewable(range)` goal, `preserve` accepts a complete footprint from a
fresh uninitialized local declaration, an assignment whose effects touch
only automatic storage, or a return with only automatic-storage effects,
including scope cleanup. The latter footprints require unchanged heap
retirement information. Prove separation from the footprint and supply the
exact entry viewability fact. The conclusion is a live-storage fact for the
same range at the exit, including for symbolic `uint64` byte ranges. At the
published outcome a return can also include one recorded retirement of a
provably distinct automatic object after the statement's exit snapshot.

For equality goals, use an ordinary `have` to establish the equality, then
`rewrite` and `close()` to carry a proposition across the change. The tactic remains
`preserve(...)` in expansion. Unavailable separation, an unsupported observation,
or mismatched endpoints is a local refusal. This tactic is distinct from a
loop's `maintain by { ... }` proof block.

- Read equality. [`preserve_step_carries_a_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_step_carries_a_fact.md) and [`memcpy_then_terminator_keeps_copied_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_then_terminator_keeps_copied_bytes.md)
- Resource field equality across two statements. [`multi_write_resource_transport_expansion.md`](https://github.com/clicklang/click/blob/master/mdtests/multi_write_resource_transport_expansion.md)
- Range viewability. [`cstr_plain_char_kernel_requirement_reaches_callee.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_plain_char_kernel_requirement_reaches_callee.md)

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

Use `close()` to select the published containment, then apply
`separation::contains_refl` and `separation::separate_restrict` with the explicitly
available resource separation. For several inputs, first use
`separation::separate_star`. The resulting footprint separation is an ordinary
premise of `preserve`; this route needs no footprint normalization.
See `mdtests/recursive_call_footprint_containment.md` and
`mdtests/recursive_call_pair_footprint_containment.md`.

For one checked transition, establish each affected member's exact separation
from `B`, then close `separate(region.footprint, B)` with `close()`.
Restrict parent separations or rewrite aliases in preceding proof steps.
Spatial ranges use byte coordinates and retain their range-validity
conditions. Empty memory ranges, distinct storage blocks, and token/memory
pairs are disjoint directly. For several transitions, write an individual
`preserve(...)` proof for each transition and compose their equalities with
`rewrite` and `close()`.

`preserve` supports complete pointer, 8/16/32/64/128-bit integer, and abstract
typed memory observations. It also preserves a selected field of a named owned
resource: cite `separate(region.footprint, r)` and write
`preserve(r, region);` under a goal such as
`r.field == at(region.entry, r.field)`.
Field lowering supplies the instance identity and field selector. The primitive
reads that field from the footprint's persistent entry and exit resource contexts
by identity; it does not unfold the resource or enumerate its other fields.
Split expressions involving different resource fields into individual links.
Supported field values include algebraic values, mathematical `Integer`,
abstract C values, pointers, and 8/16/32/64-bit integers.
Byte and 16-bit reads retain their storage widths when C promotes the
comparison to `int32`. For a promoted comparison, both operands must
widen from the same byte or 16-bit type. A 128-bit equality retains both
operands' signed or unsigned Integer observations. The result is oriented
after-to-before. Logical read producers
retain their complete typed values under the exact version point, address, and read
type. `preserve` looks up the selected observations and constructs their equality;
it does not reconstruct values from cached cells or memory derivations. This
includes pointers whose address and provenance have different internal names.
Read observations are retained only while lowering and applying an explicit
`preserve(...)` step, then released. Nested applications have isolated tables. Ordinary
checking does not retain these observations. Missing observations fail locally;
no alias or history fallback runs.
Pointer preservation also accepts address equality when the pointer domains
already agree. Equality composition uses ordinary `rewrite` and `close()` steps.
Footprints can record non-memory resources, symbolic release spans, and
multiple mutable call resources. Wide-index memory ranges are supported for
viewability preservation.
Joined branch/loop footprints still need
producer integration; use recorded individual transitions where available.
An unavailable premise, unsupported rule, or mismatched endpoint fails locally.

**Checked examples:** [`preserve_pointer_read.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_pointer_read.md), [`preserve_resource_field.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_resource_field.md).

### Ordinary arithmetic proofs

Arithmetic automation expands to ordinary proofs. Arithmetic operations correspond to named laws, applied with explicit `using` premises:

| Arithmetic operation | Ordinary law |
| --- | --- |
| Add two non-strict Integer bounds | `integer::add_le(a, b, c, d)` |
| Subtract two Integer bounds with the right order reversed | `integer::subtract_le(a, b, c, d)` |
| Scale an inequality by a nonnegative factor | `integer::multiply_order_nonnegative(a, b, factor)` |
| Turn strict order into a successor bound | `integer::lt_step_le(a, b)` |
| Restore strict order from a successor bound | `integer::step_le_lt(a, b)` |
| Combine non-strict order with disequality | `integer::le_ne_lt(a, b)` |
| Move an order to or from a difference | `integer::le_difference(a, b, value)`, `integer::difference_le(a, b, value)` |
| Round an Integer upper bound | `integer::round_down_le(value, bound, divisor, remainder)` |

Integer composition plans expand their premise, addition, scaling, and
equality-direction nodes into ordinary `have`, `apply(...)`, `rewrite`,
and `close()` steps. Each intermediate fact is established once and later
nodes reuse it. Context-free identities relate the plan's flat affine forms
to the written operands. Expansion uses checked `normalize()` when the
bounded algebra emitter cannot spell an identity. Integer antisymmetry uses
`integer::le_antisymmetric`.

Strict Integer premises and goals use the successor-order law. Linear
refutations that use the negated goal once become direct compositions;
other refutations open a negated-goal scope with `intro` and close its contradiction. Type
ranges and constant-divisor quotient, shift, and remainder bounds use
`close()`. Rounding and endpoint exclusions use ordinary Integer laws.
Machine operation and cast identities use `close()` after their exact Integer
bounds have been proved. Literal shifts and nonnegative literal masks expand
to these leaves, explicit product bounds, and rounding laws. Numeric conditionals
at the root or nested inside arithmetic, casts, observations and call arguments
expand to `close()` arm equations and rewrites when their guards are selected.
Outer arms are selected before examining their contents; an inactive arm is
not detached and evaluated. Multiple conditionals are reduced in source order,
with at most 64 rewrites and 4096 visited source nodes under the solve deadline.
Binders and historical point expressions keep their scope and are not traversed.
Arithmetic after selection uses ordinary emitters. Omitted guards remain
unavailable to `close() using`, even when present in the ambient context.
See [`nested_conditional_explicit_arm_equations.md`](https://github.com/clicklang/click/blob/master/mdtests/nested_conditional_explicit_arm_equations.md).
Boolean and constructor-valued conditionals use the same arm equations.
For example, from `flag == true`, `close()` proves
`(if flag { Some(x) } else { None }) == Some(x)`. Nested selections expose
one arm at a time and retain each proof as an explicit rewrite. A Boolean
comparison with a literal can also use the selected arm's exact truth fact.
Definition refutations whose unfolding also needs constructor-match reduction
can retain a checked `normalize() using` step with the selected branch facts.
See [the explicit arm proofs](https://github.com/clicklang/click/blob/master/mdtests/non_numeric_conditional_arm_equations.md).

Scalar signed interval claims, operation bounds, and narrowed casts expand
through selected Integer and machine-observation proofs, without `normalize()`.
Their intermediate facts replay with implicit solving disabled. Widened unsigned
sums such as `(a as int64) + (b as int64) <= 30i64`, from selected
`a <= 10u32` and `b <= 20u32`, also expand through exact operation ranges,
widening identities, and ordinary Integer arithmetic. Each operand is widened
before addition. The route supports uint8/uint16 source ranges, uint32 values
above `INT32_MAX`, and nonnegative int64 constants through `UINT32_MAX`.
Missing selected bounds and bounds one below the attainable sum are refused.
See [`widened_unsigned_sum_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/widened_unsigned_sum_bounds.md)
and its adjacent refusal fixture. Exact type bounds on observations at
program points expand to `close()` when the bound follows from the type.
Other retained-read and history obligations keep the compatibility normalizer
with their selected facts and version points. Other specialized selected rules
normalize from explicit inputs, while polynomial
search emits separate distribution and rewrite steps. All library proofs use
ordinary tactics. The [library reference](../library/index.md#foundational-integer-order-axioms)
states the named laws' exact guards.

Integer inequality composition writes the equalities that convert bounds
to and from `left - right <= 0`. `close()` checks the local equalities,
and the algebra emitter writes named laws and rewrites for coefficient
rearrangements. A cited fact that is false by computation can close with
`contradiction(fact)` directly.

Bounded cast identities expand by proving the exact destination range from
the selected bounds and then closing the observation equality with
`close()`. Native and Integer spellings of the source bounds can be cited.
For example, a signed value bounded from 1 through 100 keeps its Integer
value when cast to `uint32`.

Scalar-pointer offset translation expands through the named
`integer::<pointee>_pointer_translate_int32` /
`<pointee>_pointer_translate_uint64` laws, explicit
Integer displacement equalities, and proved pointer-association helpers.
Nested element offsets are associated only after proving the native index sum
is exact: signed definedness or an unsigned nonwrapping upper bound. This
route supports scalar pointees with int32/uint64 indices and preserves element
strides and the selected pointer relation. It uses at most 64 offsets per
source chain, 64 selected ambient premises, and 4096 emitter operations under
the solve deadline. Mixed symbolic
index families and unsupported pointer forms retain compatibility behavior.
See [`pointer_offset_explicit_bridge.md`](https://github.com/clicklang/click/blob/master/mdtests/pointer_offset_explicit_bridge.md).

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
  while preserving the point it is stated at and its byte span. A cited shifted view
  whose span is `(i + 4) - i` also covers the same address with a literal
  four-byte span; constant endpoint differences are compared in the
  span's own modular arithmetic.
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
- When the equality's left side contains a read, the occurrence in the
  goal must read the same version. If two versions are known to agree,
  state that equality first and use it to rewrite the occurrence.

**Outside it**, with what to write instead:

- A proposition that is not an equality (`x != y`, `x <= y`): there is no
  substitution by order; use `close() using` or `normalize() using`.
- An equality available only as an implication's consequent: establish it
  with `have` or `apply(fact)` first.
- A goal without an occurrence of `L`, including a different association or
  a constant that lowering folded away: rewrite by the equality as the goal
  writes it, or in the other direction.
- A quantifier that binds a variable of `P`: that subtree is left unchanged,
  and if nothing else changes the step is refused; `intro` first.
- An `Integer` equality under an internal fold or match binder, and an
  integer equality with a composite left side under the binder of a `match`
  arm: `unfold` or `match` first. An unfolded `match` the rewrite cannot
  enter is left exactly as it was.
- Rewriting a fact rather than the goal: rewrite a goal that restates it,
  then close with `close()`.

**Failure, checking, and tools:**

An unavailable equality, a missing occurrence, a blocked binder, or an
ill-typed rewrite fails, naming the equality as lowered beside the goal.
Click performs that rewrite only; expansion is unchanged, and profiling
charges the affected expression.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`equality_rewrite_scalar_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/equality_rewrite_scalar_bounds.md), [`integer_equality_rewrite.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_equality_rewrite.md), [`algebraic_symbolic_values.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_symbolic_values.md), [`rewrite_through_a_loaded_pointer_field.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_through_a_loaded_pointer_field.md), [`rewrite_pointer_inside_integer_read.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_inside_integer_read.md), [`rewrite_pointer_null_into_an_address.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_null_into_an_address.md), [`rewrite_pointer_into_a_shifted_byte_view.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_into_a_shifted_byte_view.md), [`rewrite_keeps_a_match_it_cannot_substitute_through.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_keeps_a_match_it_cannot_substitute_through.md), [`rewrite_replaces_only_a_parsed_occurrence.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_replaces_only_a_parsed_occurrence.md)

### Introducing a binder or premise

**Forms:** `intro() { ... }` or `intro(name) { ... }` for a named universal binder.

**Core.** For an implication, the block assumes the antecedent and proves
the consequent. For a universal, it fixes an arbitrary value and proves
the body at that value. The closing brace discharges the original goal and
ends the scope of the premise or binder. In a grouped contract proof the
next tactic can then work on the next claim. The flat forms `intro();` and
`let name = intro();` are also accepted.

With `intro()`, a universal's variable keeps the name its quantifier wrote.
An earlier binding of the same name stays readable as `outer.name`. That
includes a range quantifier's
variable in a `have` stated between C statements
([`intro_names_a_range_variable_in_a_have_between_statements.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_names_a_range_variable_in_a_have_between_statements.md)). A known C/C++ record binding named `outer` keeps ordinary `outer.field`
access in a proof; it is not parsed as the shadowed-binder qualifier.

**Accepts** a goal whose lowered head is one of these:

- `A implies B`: `A` becomes a fact and the goal is `B`. A conjunction `A` is
  available conjunct by conjunct, so `close()` closes `0 <= k` after
  introducing `0 <= k and k < n`. `implies` groups to the right, so
  `A implies B implies C` takes two `intro()`s.
- `forall (x: T) { B }` for an `int32`, `uint64`, pointer, `Integer`, or
  `spec enum` binder: `x` is a new variable in scope and the goal is `B`.
- `(lo..hi).all(|x| { B })`: one scoped introduction binds `x` and makes
  both `lo <= x` and `x < hi` available while proving `B`. Use one nested
  block per range and a separate block for an implication written in `B`.
  Flat introductions take two steps, one for the binder and one for membership.
- An implication lowering inserted in front of a written body, such as a
  path fact: `intro()` adds the premise and keeps the written goal focused.
  If such an implication sits between a range binder and the membership
  premise, introduce those premises explicitly inside the binder's block.
  Definedness requirements for evaluated expressions must be established
  separately.
**Outside it**, with what to write instead:

- A negation or disequality: use a proof `if` on the denied condition. Refute
  that condition in the first arm and use the complementary fact in the
  second arm.
- A conjunction: `all`. A disjunction: prove one disjunct with `have` and
  close with `close()`.
- An existential, including `(lo..hi).any(...)`: `witness`.
- A comparison or other leaf: `normalize()`, `close()`, or `close() using`.

**Failure, checking, and tools:**

A refusal names the goal's shape, such as "got a condition fact" or "got a
conjunction". Click checks the introduction and the proof of its body. Expansion preserves
the written block and expands any smart steps inside it.

**Checked examples:** [`scoped_intro.md`](https://github.com/clicklang/click/blob/master/mdtests/scoped_intro.md), [`copy_n_segment_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/copy_n_segment_invariant.md), [`quantifier_intro_nested_connectives.md`](https://github.com/clicklang/click/blob/master/mdtests/quantifier_intro_nested_connectives.md), [`integer_forall_intro.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_forall_intro.md), [`an_introduced_variable_hides_a_parameter_of_its_name.md`](https://github.com/clicklang/click/blob/master/mdtests/an_introduced_variable_hides_a_parameter_of_its_name.md)

### Naming an introduced binder

**Form:** `let name = intro()`

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
  forms (`k >= 0`, `3 > k`, `not (k >= 3)`); a `uint64` binder with no
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
- An instance held only in another form (`0 == f(0)` for `f(0) == 0`) or
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

**Forms:** `contradiction()` and `contradiction(P)`.

**Core.** `contradiction()` closes the focused branch, whatever its goal,
when `false` is already established. `contradiction(P)` closes the branch
from the selected proposition and its negation. Both use indexed lookups
and context-free checks.

**Accepts** `P` when both halves hold:

- `P` is held: it is an available fact in any of its forms (written,
  mirrored, such as `0 > x` for `x < 0` or `3 == x` for `x == 3`, or at the
  other polarity), possibly as a conjunct of a held conjunction; or `P` is a
  conjunction whose conjuncts are each available.
- Its negation is held: `not P` is an available fact; or `P` is a comparison
  and the opposite comparison of the same operands is (`x != 3` for
  `x == 3`, `x >= 0` for `x < 0`, `x <= 5` for `x > 5`); or one of the fixed
  equivalent forms of its negation is, including the mirrored one
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
  `have x >= 0 by close() using { x >= 1; };`, or close with
  `close() using { ... }`.
- A `not P` that needs scaling or overflow reasoning, such as `2 * x == x + x`
  or `x + 1 > x` at a C width: `close() using { ... }`.

**Failure, checking, and tools:**

An empty call without an established `false` is refused. For a selected
proposition, the refusal names the missing half. `contradiction(false)`
is also accepted, and expansion prints it as `contradiction()`. Profiling
charges one leaf for either form.

**Checked examples:** [`an_antecedent_normalization_refutes_closes_its_implication.md`](https://github.com/clicklang/click/blob/master/mdtests/an_antecedent_normalization_refutes_closes_its_implication.md), [`surface_syntax.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/surface_syntax.rs),
[`contradiction_opposite_comparison.md`](https://github.com/clicklang/click/blob/master/mdtests/contradiction_opposite_comparison.md),
[`uint64_branch_negation_refutes_the_other_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_branch_negation_refutes_the_other_arm.md), [`function_match_arm_closes_by_contradiction_after_a_have.md`](https://github.com/clicklang/click/blob/master/mdtests/function_match_arm_closes_by_contradiction_after_a_have.md), [`function_match_arm_contradiction_needs_a_refuted_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/function_match_arm_contradiction_needs_a_refuted_fact.md)

### Universal instantiation

**Form:** `instantiate(F, value, ...)`

**Specialized.** Supply a nonempty prefix of values for an established
universal fact, in binder order. For example, `instantiate(F, x, n)`
specializes `forall (i: int32) { forall (j: uint64) { B } }` at `x` and
`n`. Each substitution adds its resulting fact, including any implication
guards. Supplying fewer values leaves a universal available. Each
argument must have a remaining outer universal binder.

**Accepts:**

- An available `forall (k: T) { B }` fact, including a leaf conjunct, up to
  typed binder renaming. `T` may be `int32`, `uint64`, `Integer`, or a
  supported pointer type. Range quantifiers `(lo..hi).all(|k| { B })` use
  their ordinary guarded universal representation.
- A value of the binder's type: use `3u64` for `uint64`, an `Integer`
  expression such as `to_integer(x)` for `Integer`, and a correctly typed
  pointer for a pointer binder.

A range quantifier retains the range condition. The selected values are
captured at the operation's program point. Any `old` or `at` in the body
reads its own state while using those captured values.

For `forall (k: int32) { 0 <= k implies f(k) >= 0 }`, instantiating at `x`
adds `0 <= x implies f(x) >= 0`. If `0 <= x` is already an exact fact,
ordinary unit propagation also makes `f(x) >= 0` available. A guard can be
proved later with `have 0 <= x;`, with the same result. When a guard only
follows through equality or arithmetic, prove that exact guard with `have`;
instantiation performs no premise search or guard discharge.

**Outside it:** a universal not yet established must be proved first with
`have`. A value of another carrier needs a conversion. The former `using`
list is rejected; write ordinary guard proofs instead.
The loop preservation checker currently supports instantiation inside
`have proposition by { ... }`. Supporting a standalone instantiation in
`maintain` requires the checker to carry the added fact between execution
steps.


**Failure, checking, and tools:**

An unavailable source names the missing quantified fact. A non-universal or
wrongly typed argument is refused locally. Missing guards do not cause an
instantiation error: they remain in its resulting implication. After all
arguments have checked, the step closes the goal if it added that exact
fact. Use `close()` to close a consequence made available by propagation.
Expansion retains the argument list and any needed guard proofs as ordinary
`have` blocks. Checking does
indexed source lookup and substitution over the selected body, without scans
of unrelated facts.

**Checked examples:** [`instantiate_preserves_guards.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_preserves_guards.md), [`instantiate_propagates_known_guards.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_propagates_known_guards.md), [`instantiate_guard_proved_through_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_guard_proved_through_equality.md), [`instantiate_does_not_prove_guarded_conclusion.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_does_not_prove_guarded_conclusion.md), [`instantiate_rejects_using_list.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_rejects_using_list.md)

### Fact application

**Form:** `apply(fact)`

Apply an available implication, written in full or cited by a `have` fact
name. For `A implies B implies C`, the result is `C` after proving `A` and
`B`. The source must already be available; application does not unfold it or
search for an implication with that conclusion.

Established antecedents discharge directly. The implicit solver handles open
antecedents in ordinary `have` scopes. Expansion retains those proofs before
the bare application, which replays using the established facts.
Conjunctions and quantified conclusions are retained whole. Later written
steps see the established conclusion, as after theorem application.

<!-- verified-example: mdtests/apply_implication_fact.md -->
```click
have h: x > 0 implies y > 0 by close();
apply(h);
```

An unavailable source, a source of the wrong shape, or an unproved antecedent
causes application to fail.
Named fact scope and program-point selectors retain their ordinary meaning.
Theorem calls keep their existing `apply(theorem(args))` spelling.

**Checked examples:** [`apply_implication_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_implication_fact.md).

### Theorem application

**Form:** `apply(theorem(args))`

**Core.** Apply a verified global theorem at the written arguments. Click
generates obligations from the instantiated theorem requirements and argument
evaluation, in pure proofs, at the execution frontier, and on returned
outcomes. Available facts and direct checking close these obligations,
including evaluation conditions that are already established in scope.
Ordinary implicit `close()` proves any remaining obligations. You can
establish a missing fact first with `have P by { ... }`.

**Failure, checking, and tools:**

An unknown theorem, type mismatch, or unproved obligation fails without
changing resources. A missing obligation names the proposition to prove.
Expansion retains any needed `have` proofs and writes the bare
`apply(theorem(args))`. Replay checks generated obligations using ordinary
availability and evaluation rules.

**Checked examples:** [`pure_theorem_apply.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_theorem_apply.md), [`pure_apply_obligations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_apply_obligations.md), [`apply_cites_a_premise_stated_first.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_cites_a_premise_stated_first.md)

### Unfolding pure functions

**Form:** `unfold(function(args))`, or `unfold(at(point, function(args)))`

**Core.** Expose one defining equation for the exact pure-function call at the
current proof state and refresh the current goal through that one layer.
Library field accessors such as `slice::len` and `slice::as_ptr` follow the
same rule as locally defined functions: a constructor argument alone does
not unfold the call.
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
  equation just added. After that only `close()` or `normalize()`
  may follow.
- At a C execution frontier, adds the equation and leaves the frontier.
- With `at(point, ...)`, adds `at(point, function(args)) == at(point, body)`:
  the defining equation with the arguments' array contents read at `point`,
  and rewrites occurrences of `at(point, function(args))`
  (`mdtests/unfold_at_a_point_opens_a_pure_function_there.md`). `close()`
  evaluates a call that a fact names at a point, such as a postcondition at
  the call's entry, with this form.
- For an `Integer` range-fold body, a decided empty range exposes its initial
  value; a decided nonempty range exposes its append-last-cell equation over
  the same function at the predecessor endpoint. The whole-call and predecessor
  defining equations remain available alongside that law. An available exact
  predecessor-range guard also selects the append form, including `Integer`
  index folds. Any missing law guards
  are ordinary obligations, proved by the implicit solver and retained by expansion.
  The append form requires the end to be a function parameter that its start,
  initial value, and body do not read. When the
  range case is undecided (including no available predecessor guard), or that
  form cannot name a predecessor call, ordinary
  unfolding retains the raw defining equation; split the range case or prove
  the needed equation explicitly. A goal that already states the defining
  equation continues to unfold that definition directly.

**Outside it**, with what to write instead:

- A refreshed goal that became `true` or reflexive, such as `x + 1 == x + 1`:
  it stays open; close it with `normalize()`.
- A call whose arguments mention a quantifier's binder before it is
  introduced: `intro()` first.
- More than one layer: `unfold` again at the exposed call.
- A `using` list: state supporting facts before `unfold`; its remaining guards
  are ordinary obligations.

The refreshed goal can also come out further simplified, as the lowering of
the rewritten goal does: `n + k - k` over `int32` reduced to `n` in one probe.
That is not guaranteed; follow with `normalize()` or `close() using { ... }` when the
goal needs it.

**Failure, checking, and tools:**

An unknown function ("unknown pure function `h` in `unfold`") or an argument
count mismatch fails; an argument that does not lower at this point fails with
"could not lower defining equation". Expansion retains any generated guard proofs before the checked `unfold`;
replay needs no implicit solver. Profiling charges the arguments, one body
layer, and any implicit guard proofs.

**Checked examples:** [`library_field_accessors_unfold_after_a_constructor_rewrite.md`](https://github.com/clicklang/click/blob/master/mdtests/library_field_accessors_unfold_after_a_constructor_rewrite.md), [`library_field_accessors_need_their_defining_equation.md`](https://github.com/clicklang/click/blob/master/mdtests/library_field_accessors_need_their_defining_equation.md), [`unfold_fold_integer_callback_uses_ordinary_obligations.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_integer_callback_uses_ordinary_obligations.md), [`unfold_fold_empty_uses_ordinary_obligations.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_empty_uses_ordinary_obligations.md), [`unfold_fold_int32_uses_ordinary_obligations.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_int32_uses_ordinary_obligations.md), [`pure_function_unfold.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_function_unfold.md), [`unfold_rewrites_each_occurrence_of_the_exact_call.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_rewrites_each_occurrence_of_the_exact_call.md), [`normalize_evaluates_a_substituted_conversion.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_evaluates_a_substituted_conversion.md), [`a_step_after_an_unfold_that_closed_the_goal_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/a_step_after_an_unfold_that_closed_the_goal_is_refused.md), [`unfold_function_after_integer_intro.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_function_after_integer_intro.md), [`unfold_function_integer_shadow.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_function_integer_shadow.md), [`unfold_rejects_using_list.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_rejects_using_list.md)

### Constructor matches

**Form:** `match value [ensuring { ... }] { Type::Variant(fields) => { ... } ... }`

**Core.** In a pure proposition proof (including structural-induction arms), or
at any execution frontier the proof has reached — unchanged function entry,
after executed statements, or a loop's `maintain` body — split an ADT of any
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
`maintain` body with nothing written after the `match`, each live arm must
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

Tactics written after a `match` in a `maintain` body are checked once:
straight-line arms that end in one state rejoin as in a function body, and two
arms still live at one point that end apart are refused
(`mdtests/loop_body_proof_match_shared_continuation.md`). With `ensuring`, arms
that end apart rejoin inside the body, as the arms of a `branch` do, and those
tactics are checked once on the one path that leaves the `match`
(`mdtests/loop_body_proof_match_ensuring_rejoins.md`); a proof `if ... ensuring`
in a `maintain` body rejoins the same way.

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

**Form:** `let ih = induct(n)`

**Core.** At a pure theorem's original goal, introduce a strong induction
hypothesis named `ih` over an `int32` or `uint64` parameter `n`. The signed measure
requires a nonnegative domain; the unsigned measure has that domain intrinsically.

**Accepts** a pure theorem `ensures ... by { ... }` script containing one
top-level `let ih = induct(n)`, when:

- `n` names a theorem parameter of type `int32` or `uint64`. Other parameters
  of any type, including `Integer`, may sit beside it.
- For `int32`, a fact on hand bounds `n` itself below by a constant: `n >= c`
  or `c <= n` with `c >= 0`, or `n > -1`. A requirement stated as a
  conjunction, such as `requires n >= 0 and n <= 10;`, supplies it. A `uint64`
  measure needs no domain fact.

It adds one fact, `ih`: for every `m` of the measure's type, `m >= 0` (signed
only), `m < n`, and every theorem requirement at `m`, together with the span
halves of each range that requirement names at `m`, imply the theorem's goal
at `m`. Every other parameter keeps its current value. The goal is unchanged.
Earlier helper proofs may precede `induct`; the hypothesis is unavailable
before its declaration. Use `apply(ih(m))` at the top level and inside nested
`if`, `all`,
`cases`, `have`, and `match` blocks.

**Outside it**, with what to write instead:

- A second `induct` in the same script: induct once.
- A changed goal, after `intro` or a goal-changing `rewrite`: introduce
  induction while the original theorem goal remains focused.
- A parameter of another C width (`uint32`, `int64`, ...), an `Integer`, or an
  algebraic value: induct on an `int32` or `uint64` parameter, or use
  `let ih = induct(xs);` followed by `match xs { ... }` for an algebraic one.
- A signed domain that only follows from other facts, such as `0 <= m` and
  `m <= n`: prove `have n >= 0;` before `induct`.
- `induct` in a C function proof: state the property as a pure theorem and
  apply it.

**Failure, checking, and tools:**

An unsupported parameter type, changed goal, repeated induction, or unproved
signed nonnegative domain fails with a message naming the case. `induct` in
a C execution proof reports a `tactic error`. Click opens the induction
rule during checking and profiling charges the structural setup.

**Checked examples:** [`scalar_induction_after_helper_facts.md`](https://github.com/clicklang/click/blob/master/mdtests/scalar_induction_after_helper_facts.md), [`pure_induction_countdown.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown.md),
[`an_induction_hypothesis_applies_inside_a_have.md`](https://github.com/clicklang/click/blob/master/mdtests/an_induction_hypothesis_applies_inside_a_have.md),
[`an_induction_hypothesis_applies_inside_match_arms.md`](https://github.com/clicklang/click/blob/master/mdtests/an_induction_hypothesis_applies_inside_match_arms.md),
[`an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.md`](https://github.com/clicklang/click/blob/master/mdtests/an_induction_hypothesis_applies_in_a_have_and_a_match_nested_either_way.md),
[`uint64_measure_induction_counts_a_range_fold.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_measure_induction_counts_a_range_fold.md),
[`pure_induction_keeps_other_parameters_fixed.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_keeps_other_parameters_fixed.md),
[`pure_induction_requires_nonnegative_domain.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_requires_nonnegative_domain.md),
and [`scalar_induction_domain_needs_a_bound_on_the_measure.md`](https://github.com/clicklang/click/blob/master/mdtests/scalar_induction_domain_needs_a_bound_on_the_measure.md).

### Algebraic induction

**Form:** `let ih = induct(xs);` followed by
`match xs { Type::Variant(fields) => { ... } ... }`.

**Core.** Prove a pure theorem for a recursive algebraic parameter by exhaustive
constructor cases; each immediate recursive field admits `ih(field)`, and
`ih(field, other, ...)` states the theorem at that field and any well-typed
terms in the remaining parameter positions.

The declaration preserves the goal and introduces the local hypothesis at
its written position. Helper proofs may precede it or separate it from a
`match`. A match on the inducted parameter exposes hypotheses for that arm's
immediate recursive fields; matches on other values do not. The match may
appear inside `if`, `have`, or other ordinary proof blocks, and may use the
ordinary shared continuation after its arms. Field names remain arm-local.

The original theorem goal must still be focused at each declaration. All
structural declarations in one proof name the same theorem parameter and
hypothesis; a path cannot introduce that hypothesis twice. The declaration
may be in a proof block when that block is proving the original theorem goal.
Expansion can therefore copy a shared declaration into earlier branches.
Each match arm is checked by the ordinary pure-match driver, which does not accept a
join `ensuring` interface. Expansion preserves the declaration and checked
match structure and expands its helper proofs and continuations. The retired
`induct(xs) as ih { ... }` spelling is refused.

**Failure, checking, and tools:**

A missing, duplicate, unknown, or wrong-arity arm fails. Bindings are arm-local,
and `ih` rejects nonrecursive or non-immediate values in the inducted position,
a parameter list of the wrong length, and an instantiation whose substituted
requirements are unavailable. Click checks every arm; expansion recurses through
the arm certificates.

**Checked examples:** [`structural_induction_surrounding_helpers.md`](https://github.com/clicklang/click/blob/master/mdtests/structural_induction_surrounding_helpers.md), [`structural_induction_continuation.md`](https://github.com/clicklang/click/blob/master/mdtests/structural_induction_continuation.md), [`algebraic_structural_induction.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_structural_induction.md), [`algebraic_structural_induction_generalizes_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_structural_induction_generalizes_parameters.md)

### Induction hypothesis application

**Form:** `apply(ih(m))`

**Core.** Instantiate the local induction hypothesis and prove its premises.
For a scalar measure, those premises are `m < n`, `0 <= m` for a
signed measure, and the theorem's requirements at `m`. Other parameters stay
fixed. For structural induction, the inducted argument must be a recursive
field of the current arm, and the requirements are checked at the full
written parameter list.

A premise may be stated in an equivalent order form such as `n > m` for
`m < n`. Range requirements also owe their span halves. A previously stated
range supplies those halves where they are available. The ordinary implicit
solver tries any remaining premises, and a preceding `have` can supply a
premise explicitly.

The application adds the instantiated theorem conclusion and closes the
focused goal if the conclusion proves it. Expansion retains the premise
proofs as `have` steps followed by the bare application. A refusal names the
premise it could not prove.

**Checked examples:** [`scalar_induction_after_helper_facts.md`](https://github.com/clicklang/click/blob/master/mdtests/scalar_induction_after_helper_facts.md), [`pure_induction_countdown_explicit.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown_explicit.md), [`induction_hypothesis_cites_a_listed_range_with_its_span.md`](https://github.com/clicklang/click/blob/master/mdtests/induction_hypothesis_cites_a_listed_range_with_its_span.md), [`induction_hypothesis_owes_the_range_span.md`](https://github.com/clicklang/click/blob/master/mdtests/induction_hypothesis_owes_the_range_span.md).

### Intermediate facts

**Form:** `have P by { ... }`

**Core.** Open a nested goal `P`; on success, add `P` to the surrounding context
without changing its execution frontier. `have P;` without a proof is `have P by
close();`, and a one-step proof may drop the braces: `have P by T(args);`. A
`have` executes no C. On a linear `Integer` bound `close()`
refutes the integer negation from the facts connected to `P` and applies the
result as ordinary Integer law applications
([`have_by_solve_refutes_a_linear_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/have_by_solve_refutes_a_linear_bound.md)).

Connected `int32`, `int64` and `uint64` order facts are carried to `Integer` by
`close()`, since a comparison of observations is the native comparison,
and `uint64` values get their type range by `close()`; only
the selected carried facts are kept
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
does not wrap, by `close()` reading both
constant bounds of its exact value
([`solve_observes_an_operation_term_by_term.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_observes_an_operation_term_by_term.md)).

Machine equality facts are carried by rewriting, each observed value gets its
type range by `close()`, an `int32`, `int64` or `uint64`
equality goal is
proved as its observed reading once both sides are shown defined, splitting an
equality into its two bounds when needed, and a conjunction goal is split
([`solve_proves_a_conservation_equation.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_a_conservation_equation.md)).
On an implication `A implies B`, `close()` introduces `A` and closes `B`, with
this arithmetic and the searches below, as for `result == 1 implies cap ==
old(cap) + 1` on a path where the antecedent reads `true`
([`solve_proves_an_implication_whose_consequent_needs_the_solver.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_an_implication_whose_consequent_needs_the_solver.md)).
The in-range `+`, `-` and `*` identities, a product's bounds from its
operands' explicit type ranges by ordinary product-bound applications included
([`solve_observes_a_product_by_a_constant.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_observes_a_product_by_a_constant.md),
[`a_product_of_64_bit_values_is_its_exact_product.md`](https://github.com/clicklang/click/blob/master/mdtests/a_product_of_64_bit_values_is_its_exact_product.md)),
and integral-cast identities this arithmetic uses, nested ones included, are
described in [mathematical integers](../../internals/mathematical-integers.md#in-range-machine-sums-differences-and-products).

When its other strategies miss, `close()` searches chains of at most three
`rewrite` steps by the equalities connected to `P`, machine, `Integer` and
algebraic alike, each in either direction, and closes the rewritten goal by
direct closure, normalization, or a bounded recursive search.

Each rewrite is a checked step, and the search offers at most 64 equalities,
those that rewrite `P` itself first, and tries at most 256 rewrites, so a large
connected component fails promptly
([`solve_rewrites_a_constructor_term_to_its_model.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_rewrites_a_constructor_term_to_its_model.md),
[`solve_refuses_a_constructor_rewrite_that_does_not_close.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_refuses_a_constructor_rewrite_that_does_not_close.md)).

The search cites only equalities that raise at that point; a fact
from an earlier `have` or a proof `if` condition inside a pure theorem has none
and is not offered. In a pure theorem, an omitted proof of `ensures P` uses the same
closure and search as `close()`. `have name: P` also names the fact: until the end of
the enclosing block, `name` stands for `P` wherever a proposition is cited
whole, as in `using { name; }`, `have name by close();` or `contradiction(name)`, and is
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

A quantifier variable, including one named by `let name = intro()`, hides a
fact of the same name in its body. The chosen name must not reuse an active
value binding.
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

In a loop's `maintain` body the rule is the same, except that arms reaching
those tactics at different points are different paths of the C and each
is finished its own way.

At function exit the C state is fixed. When the path's facts already decide
`P`, only the matching arm runs. When `P` is open and tactics follow the `if`,
the `if` is refused, because its arms would not rejoin and what follows would
be checked once per arm (`mdtests/a_proof_if_after_execution_that_would_fork_is_refused.md`).
Write those tactics inside the arms instead
(`mdtests/a_proof_if_after_execution_closes_its_claims_in_each_arm.md`).

**Failure, checking, and tools:**

Either unfinished arm fails. Click checks both written branches; expansion
recurses into smart descendants, and profiling reports them.

**Checked examples:** [`proof_if_cases.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_cases.md), [`proof_if_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_arms_rejoin.md), [`proof_if_arms_rejoin_after_c_steps.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_arms_rejoin_after_c_steps.md), [`proof_if_ensuring_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_rejoins.md), [`proof_if_ensuring_named_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_named_resource.md), [`proof_if_ensuring_named_resource_needs_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_named_resource_needs_fact.md)

### Explicit cases

**Form:** `cases { A => { ... } B => { ... } }`

**Specialized.** Write one arm per alternative, with at least two arms. Click
checks that their disjunction holds before assuming any arm. The disjunction
groups left to right as `or` parses (`A or B or C` is `(A or B) or C`).
If it is already available, Click uses it directly. Otherwise the ordinary
obligation solver tries to prove it. For example, `x == 0 or x == y` and
`y == 1` suffice for arms `x == 0` and `x == 1`. Use `if P` to split on
a proposition you choose, since `P or not P` always holds.

Each arm assumes its own disjunct. When proving a focused proposition,
every arm proves it. At an execution frontier, `cases` joins like a proof `if`.
If tactics follow it, the arms must rejoin with the facts every arm proved
(`mdtests/cases_arms_rejoin_with_the_facts_every_arm_proved.md`,
`mdtests/cases_arms_that_do_not_rejoin_are_refused.md`); an arm that reaches
function exit finishes its own path
(`mdtests/cases_at_a_frontier_finishes_each_arm.md`). In a loop's `maintain`
proof its arms must rejoin: each arm closes its own back edge, and the
rejoined path's back edge is then closed again with only the facts every arm
proved, so an arm that needs its own fact there proves the invariants at the
next iteration, the same proposition in every arm
(`mdtests/a_preserve_cases_rejoin_keeps_only_the_facts_every_arm_proved.md`,
`mdtests/a_preserve_cases_arm_keeps_a_fact_every_arm_proves.md`). At function exit it splits the path there as a
proof `if` does: when the path's facts decide a disjunct only that arm runs;
otherwise Click establishes the same exhaustiveness obligation and splits the
path into one case per arm (`mdtests/cases_after_execution_splits_each_outcome_path.md`,
`mdtests/cases_after_execution_takes_the_decided_arm.md`). Tactics written
after a `cases` that forks are refused
(`mdtests/cases_after_execution_that_would_fork_is_refused.md`).

**Failure, checking, and tools:**

An unproved exhaustiveness obligation or unfinished arm fails. Expansion
retains any proof of the disjunction as a preceding `have` and expands each
arm. Profiling reports the descendant tactics.

**Checked examples:** [`cases_proves_equivalent_alternatives.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_proves_equivalent_alternatives.md), [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`cases_in_have_before_and_after_execute.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_in_have_before_and_after_execute.md), [`cases_at_a_frontier_finishes_each_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_at_a_frontier_finishes_each_arm.md), [`cases_arms_rejoin_with_the_facts_every_arm_proved.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_arms_rejoin_with_the_facts_every_arm_proved.md), [`cases_at_a_frontier_requires_its_disjunction.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_at_a_frontier_requires_its_disjunction.md), [`cases_after_execution_splits_each_outcome_path.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_after_execution_splits_each_outcome_path.md), [`cases_after_execution_requires_its_disjunction.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_after_execution_requires_its_disjunction.md)

### Scoped resource opening

**Form:** `with(resource) { ... }`

**Specialized.** A `with` block gives temporary access to one layer of a
composite resource's body and checks that the resource is restored on every
path out, including a function return. For an ordinary named instance,
`with(c) { ... }` selects the same instance as `unfold(c)`. The scope must
restore its original identity and field values. If the proof already restored
that exact instance with `fold(c)`, the scope closes without another fold.
For a named parent, `with(r)` exposes its children under paths such as
`r.child`. The closing fold takes those same children back. Nested `with`
blocks can use a child path directly.

Use a family call for unnamed resources, including population members and
viewed resources. Opening and restoring a population member preserves its
membership and count. Operations inside the block can change the population
under the usual authority rules. A viewed resource gives read-only access.
A model `match` inside the block uses the ordinary checked
constructor arms and joins: terminal arms each restore the resource at return;
an `ensuring` interface can rejoin before the block closes.

**Failure, checking, and tools:**

A missing resource, an undecided guard, or failure to restore the body fails. A
body fact the closing fold leaves open is proved by the implicit closer, which
expansion writes as `have` steps at the end of the block. To supply a closing
proof by hand, put the `have` there yourself, after any execution that
establishes the fact. This also works when the block reaches function exit.
Expansion can write `fold(c)` after the closing facts in a returning arm so
the remaining outcome proof sees the restored instance.
A trailing `by` after the block is refused.

**Checked examples:** [`resource_population_open.md`](https://github.com/clicklang/click/blob/master/mdtests/resource_population_open.md), [`open_scope_model_match_terminal.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_terminal.md), [`open_scope_model_match_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_rejoins.md), [`open_scope_model_match_rejects_bad_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_rejects_bad_arm.md)

**Checked closing examples:** [`open_named_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/open_named_resource.md), [`with_accepts_an_already_restored_instance.md`](https://github.com/clicklang/click/blob/master/mdtests/with_accepts_an_already_restored_instance.md), [`open_named_resource_requires_restoration.md`](https://github.com/clicklang/click/blob/master/mdtests/open_named_resource_requires_restoration.md), [`open_closing_fact_inside_block.md`](https://github.com/clicklang/click/blob/master/mdtests/open_closing_fact_inside_block.md), [`open_trailing_by_is_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/open_trailing_by_is_rejected.md)

### Existential witnesses

**Form:** `witness(value, ...);`

**Specialized.** Write it for an existential goal, supplying values for its
outermost binders in declaration order. Continue with the instantiated body.
One `witness` can supply every binder of `exists (x: T, y: U) { ... }` or
just a nonempty prefix, leaving the remaining existential goal open.

**Accepts** a goal whose outermost form is `exists (name: T) { B }` or
`(lo..hi).any(|name| { B })`, in a pure theorem or a C proof, when:

- Values follow the outermost binders: `witness(3, 4)` on
  `exists (x: int32, y: int32) { ... }` takes `x`, then `y`.
  `witness(3); witness(4);` has the same effect. Intermediate proof steps
  may appear between them. Binder names do not appear in the tactic.
  Remaining binders keep their declared types, including when an Integer
  binder precedes an enum binder.
- Each value has its binder's type: a C integer of exactly that type (`3u64`
  for `uint64`), a pointer, an `Integer` expression such as `0` or
  `to_integer(n)` for `Integer`, or an algebraic value of that datatype.

The goal becomes `B` with the value substituted; for `.any` it becomes
`lo <= value and value < hi` and `B`. No fact is added and the body is not
checked; prove it next.

**Outside it**, with what to write instead:

- An existential below the top of the goal, such as `A and exists ...`: split
  it with `all` first.
- A value of another type, such as an `int32` variable for a `uint64` or
  `Integer` binder: convert it (`to_integer(n)`) or write the suffixed literal.

**Failure, checking, and tools:**

An empty argument list, ill-typed value, or nonexistential goal fails.
Extra arguments fail when no existential binder remains. A nonexistential
pure goal reports "`witness` requires an existential proposition goal".
Click records the exact witness; expansion prints `witness(value)` steps,
and profiling charges one instantiation per value.

**Checked examples:** [`witness_preserves_remaining_binder_types.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_preserves_remaining_binder_types.md), [`witness_values_follow_the_goal_binders.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_values_follow_the_goal_binders.md), [`witness_and_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_and_choose.md), [`integer_exists_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_exists_choose.md), [`witness_reversed_values_leave_a_false_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_reversed_values_leave_a_false_goal.md)

### Obtaining witnesses

**Forms:** `let name = obtain(exists (k: Type) { P });` and
`let (a, b) = obtain(exists (x: T, y: U) { P });`.

**Specialized.** Open an established existential and name its witnesses.
The right side states the exact available proposition, up to its bound names.
The left side names the outputs in quantifier order. Their types come from
the existential. Each output and the instantiated body are available in
subsequent tactics in the same proof block. After function exit, `obtain` can
open an available fact while a resource claim is still focused. Its bindings
remain in scope for later claims in the block.

- The existential may be a requirement, a `have` conclusion, or a leaf
  conjunct of an available fact. It must be available before the tactic runs.
- One output opens the outermost binder. For example,
  `let a = obtain(exists (x: int32, y: int32) { x < y });` leaves
  `exists (y: int32) { a < y }` available.
- For a range existential, write `let k = obtain((lo..hi).any(|i| { B }));`.
  The range determines the witness type. The proof gains `lo <= k`, `k < hi`,
  and the predicate body at `k`.
- To open a historical existential, write
  `let a = obtain(at(point, exists (x: int32) { P }));`.
- Output names must be distinct and fresh in the proof block. The quantifier
  binds its own variables independently of the output names.

**Failure, checking, and tools:**

An unavailable existential, too many outputs, or an output name already in
scope fails. State an existential with `have` first if it needs a proof.
Expansion retains the `let` and its source proposition.

**Checked examples:** [`obtain_range_any.md`](https://github.com/clicklang/click/blob/master/mdtests/obtain_range_any.md), [`integer_exists_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_exists_choose.md), [`witness_and_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_and_choose.md), [`obtain_requires_the_written_existential_body.md`](https://github.com/clicklang/click/blob/master/mdtests/obtain_requires_the_written_existential_body.md)

## Integer multiplication order and division intervals

`close() using { a <= b; 0 <= k; }` proves `a * k <= b * k` by
explicit application of `integer::multiply_order_nonnegative`. A nonpositive
factor reverses the order and uses `integer::multiply_order_nonpositive`.
Commuted operands name their commutativity equations separately. The library
`scaled_product_bounds` proof uses these laws and explicit transitivity.

For Integer `truncating_quotient(n, d)` and `truncating_remainder(n, d)`,
selected constant lower/upper bounds on `n` and `d` can prove a constant
result bound when the divisor interval excludes zero. Expansion states the
numerical endpoint conditions with `close()`, proves the nonzero divisor
from the selected interval, and applies ordinary quotient/remainder lemmas.
Positive-divisor quotient bounds also accept `n <= bound * d` or
`bound * d <= n` together with `1 <= d`, including symbolic bounds.
Negative divisor intervals use the two explicit divisor-sign laws.
Remainder proofs retain both the dividend and divisor envelopes and the case
where the dividend's magnitude is smaller than every divisor's magnitude.

These expansions and their derived library proofs contain no `normalize()`
or implicit solving. Selection runs under the existing proof search budgets;
replay checks only the written arguments and premises. Missing bounds, a
zero-crossing divisor interval, and false result bounds do not justify the
interval route. Native machine definedness remains a separate obligation.

## Exact integer product bounds

Use `close() using { L <= x; x <= U; M <= y; y <= N; }` to prove
an exact bound on the mathematical product `x * y`. Each interval endpoint
and the result bound must be constant, with ordered interval endpoints.
Expansion writes four numerical corner checks with `close()`, followed by
`apply(integer::product_lower_bound(...))` or
`apply(integer::product_upper_bound(...))`. The library proofs
split on signs and apply multiplication order and transitivity explicitly;
their dependencies contain no `normalize()`. The theorem applications
reuse the established corner bounds. The same proof construction supplies
product bounds from machine operands' stated type ranges.

The authored `normalize() using` compatibility form still checks this rule.
Its checker computes `L*M`, `L*N`, `U*M`, and `U*N` using exact integers.
For an upper bound, all four must be at most `T`; for the result `T <= x * y`,
all four must be at least `T`. The rule accepts negative, zero, and crossing
intervals and bounds weaker than the exact endpoints. It reads the four selected facts and does no premise search or implicit machine-range inference.

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
| `unfold(predicate(args))` | simple | Core | Open one selected predicate application. | [Reference](#unfolding-predicates) |
| `unfold(resource(args))` | simple | Core | Open an owned resource instance. | [Reference](#unfolding-resources) |
| `fold(resource)` | simple | Core | Assemble a composite or create an ordinary token at return. | [Reference](#folding-resources) |
| `release_view(range)` | simple | Specialized | Give up one directly held produced view. | [Reference](#releasing-a-view) |
| `fold(...) by { ... }` | control | Expansion output | Supply a proof for one fold obligation. | [Reference](#folding-with-one-obligation) |
| `fold(...) { requires P by ...; }` | control | Expansion output | Supply proofs for selected fold obligations. | [Reference](#folding-with-several-obligations) |
| `unfold(resource(args)[i])` | simple | Specialized | Expose one guarded ownership slot. | [Reference](#indexed-resource-unfolding-and-folding) |
| `fold(resource(args)[i])` | simple | Specialized | Restore one guarded ownership slot. | [Reference](#indexed-resource-unfolding-and-folding) |
| `fold(resource(args)[..])` | simple | Specialized | Form the whole iterated clause from its covering range. | [Reference](#whole-clause-resource-unfolding-and-folding) |
| `unfold(resource(args)[..])` | simple | Specialized | Recover the covering range from the whole iterated clause. | [Reference](#whole-clause-resource-unfolding-and-folding) |
| `name(args, { binder: instance })` | simple | Specialized | Apply a verified tactic with resource bindings. | [Reference](#user-defined-tactic-calls) |
| `observe(resource)` | simple | Specialized | Read a resource's persistent observations. | [Reference](#observing-resources) |

Predicate calls are opaque to framing until their definitions are unfolded.
To carry such a fact across C execution, unfold the selected application before the relevant
steps and transport the unfolded definition.

### Fact transport

**Form:** `transport(P, Q)`

**Specialized.** Write it when a fact stated at an earlier state is needed at
the current one and neither `step` nor `close()` carried it. When exact source `P`
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

**Checked examples:** [`known_value_transport_expansion.md`](https://github.com/clicklang/click/blob/master/mdtests/known_value_transport_expansion.md), [`transport_model_pointer_binding.md`](https://github.com/clicklang/click/blob/master/mdtests/transport_model_pointer_binding.md)

### Transport with selected premises

**Form:** `transport(P, Q) using { R; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form
when the source alone carries the target, and list more premises here when it
does not. Derive target proposition `Q` from exact
source `P` using only the listed point and frame evidence. Available in a
pure theorem too, where the listed premises are all there is to read.

**Accepts**, in a C proof or a pure theorem, when:

- Every listed `R` is an available fact, read as every `using` list reads
  premises: exactly, under another form of the same order claim, or true
  without facts. A quantified premise may name its own binder: a call's
  postcondition held under the binder its lowering chose is cited by a written
  form with another. Listing a stated range also cites
  its two span halves.
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
`apply(separation::viewable_restrict(A, B))` steps. When both
are memory ranges with the same written base and int32 endpoints, citing
`lo <= inner_lo`, `inner_lo <= inner_hi`, and `inner_hi <= hi` instead
produces an explicit `have contains(...)` using `separation::contains_subrange` first.
These cases expand to ordinary library applications.
See `mdtests/viewable_restrict_transport_expansion.md`.

At an execution frontier, a focused equality between a read now and the same
read at a named statement's entry also expands to `preserve(R, statement(...))`
when that footprint separation is cited, the source is the earlier read's
reflexive equality, and the statement's recorded exit is the current point.
This covers memory reads and abstract resource fields. The explicit footprint
separation proof remains in the expanded script; no history search is needed
for replay. See `mdtests/single_write_transport_expansion.md` and
`mdtests/single_write_resource_transport_expansion.md`.

For several statements, cite each footprint separation in `using`. Expansion
writes one `have at(statement(i).exit, read) == at(statement(i).entry, read)`
proved by `preserve` per cited footprint, then `close()` joins the
endpoint equalities. The premises can be written in either order; they must
cover the read's path to the current point. No intermediate footprint or
separation is discovered from history, and failure of ordinary equality closure is final rather
than retrying a history search. Both memory reads and abstract resource fields
use this form. See `mdtests/multi_write_transport_expansion.md`.

A focused comparison with one read operand changing from a statement entry
to the current point uses the same preservation chain. For example,
`transport(at(statement(0).entry, *q) > 0, *q > 0) using { ... }`
first retains the earlier inequality with `close()`, proves the read
equality from the cited footprint separations, then uses `rewrite` and
`close()` to close the current comparison. This also carries a known
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
fact remains in the proof and is checked by `close()`.
See `mdtests/state_comparison_transport_expansion.md`.

When both operands are reads at earlier points, the comparison route can
preserve both: `transport(at(statement(0).entry, *q == *r), *q == *r)`.
Cite the footprint separation for each read in `using`. Expansion writes one
preservation chain per operand, rewrites both, and closes with `close()`.
Selection uses the explicitly written single-cell dereference or named
resource-field subject; it does not discover aliases or prove range containment.
Every supplied separation must be used and checked. See
`mdtests/two_read_transport_expansion.md`.
Conjunction trees of supported scalar comparisons also expand: for example,
`transport(at(statement(0).entry, *q == 7 and (*r == 8 and *s == 9)), *q == 7 and (*r == 8 and *s == 9))`.
Expansion emits a flat `all` block in goal order, with a preservation and
rewrite proof for each scalar leaf. This form handles
matching conjunction structure; selection and regrouping are described below. The source can wrap the whole tree, a
subtree, or individual leaves in `at(...)`; nested `at(...)` wrappers are not
handled by this route. Each leaf checks its earlier fact with `close()`
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
selects each target leaf by exact source text. It emits a `have` for each selected
historical leaf using `close()`, followed by its ordinary preservation/rewrite
proof, and combines the results with `all` in the target's conjunct order.
Discarded conjuncts need not remain true; only the selected reads need footprint
separations. The supplied separations are indexed once and must all be used and
checked. Whole-tree and subtree `at(...)` wrappers are supported. The exact
source text of a leaf selects one point; this route does not retry other points
or discover additional evidence. Non-comparison leaves and operand-level
`at(...)` forms remain outside this selection route.
See `mdtests/conjunction_projection_transport_expansion.md` and
`mdtests/conjunction_selection_transport_expansion.md`.

Implications also expand when source and target have matching logical structure
built from `and`, `or`, `not`, nested `implies`, and supported scalar comparison
leaves. For example,
`transport(at(statement(0).entry, (*q == 7 and *r > 0) implies (*q > 0 implies *r == 8)), (*q == 7 and *r > 0) implies (*q > 0 implies *r == 8))`
uses footprint separations for reads throughout the guard and conclusion.
Expansion retains the earlier whole fact with `close()`, proves each
selected read's preservation, then closes the whole goal with `close()`
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
  source range is established to be a valid 32-bit byte span.
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

The rule answers the same for every caller, so `close()`'s transport between points
reaches it too, and `close()` offers an `A and B` source when the goal is held at
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
prints the leaf it had and the leaf it wanted. A pure-theorem refusal prints
its propositions with the theorem's parameter names and the names the script
introduced.

Click checks that transport only; expansion is unchanged, and profiling charges
the named evidence.

**Checked examples:** [`field_derived_precise_effect_after_metadata_write.md`](https://github.com/clicklang/click/blob/master/mdtests/field_derived_precise_effect_after_metadata_write.md), [`have_viewable_prefix_of_a_range.md`](https://github.com/clicklang/click/blob/master/mdtests/have_viewable_prefix_of_a_range.md), [`sweep_maintains_a_zero_unmarked_count.md`](https://github.com/clicklang/click/blob/master/mdtests/sweep_maintains_a_zero_unmarked_count.md), [`sweep_prefix_survives_its_endpoint_store_by_solve.md`](https://github.com/clicklang/click/blob/master/mdtests/sweep_prefix_survives_its_endpoint_store_by_solve.md), [`quantified_frame_carries_a_fact_past_the_excluded_store.md`](https://github.com/clicklang/click/blob/master/mdtests/quantified_frame_carries_a_fact_past_the_excluded_store.md), [`quantified_frame_preserves_uint64_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/quantified_frame_preserves_uint64_equality.md), [`a_guarded_memset_value_claim_crosses_a_disjoint_store.md`](https://github.com/clicklang/click/blob/master/mdtests/a_guarded_memset_value_claim_crosses_a_disjoint_store.md)

### Unfolding predicates

**Form:** `unfold(predicate(args))`

**Core.** Open one layer of the selected predicate application at the current
state. Click adds its definition equivalence as an ordinary fact. If the
application is already available, its body becomes available too. Matching
occurrences in the current goal are replaced by that body.

Other applications stay opaque. Later goals receive no special interpretation;
open their applications explicitly as needed. A predicate called by the body
also stays opaque until another unfold step opens it.

Use `unfold(at(mark, predicate(args)))` to select an application at a saved
snapshot. An explicitly written quantified proposition or named fact can also
select a quantified application without introducing free binder names.

Bare predicate names are rejected. Owned resource bindings keep their existing
`unfold(binding)` form; pure functions use `unfold(function(args))`.

**Checked examples:** [`sorted_predicate.md`](https://github.com/clicklang/click/blob/master/mdtests/sorted_predicate.md), [`simple_statement_step_explicit_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_explicit_transport.md)

### Unfolding resources

**Form:** `unfold(resource(args))`

**Core.** Replace the exact held composite resource with one supported body
layer. For an `authorized` family it destroys one member and requires that
family's owned `authority(...)`; `unfold(authority(R(..)))` retires a population
whose count is zero. In `let { label: name, ... } = unfold(resource)`, the
resource definition determines what each label names. A child slot binds
the opened child instance, a C-typed field binds its folded value, and a
`let ... where` witness binds the value used to open the body. One pattern
can mix these labels whether the resource is selected by name or by a family
call. Witness bindings need a live execution frontier before function exit.
See [`unfold_binds_witness_and_child.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_binds_witness_and_child.md).

After `unfold(r)`, a child from slot `child` is held under `r.child`. An alias
such as `let { child: c } = unfold(r)` names that same instance. Resource
tactics on the path require the exposed child to be held. A model field or
`where` witness of the open parent, such as `r.tag` or `r.base`, reads the
value captured at the opening. A field read after refolding reads the new
folded instance's field. See [the checked child path example](https://github.com/clicklang/click/blob/master/mdtests/exposed_child_paths.md).

**Accepts** a declared resource with a body that the current state holds
directly, owned or viewed, in a C function proof (at the execution frontier
before exit, or at a function outcome after the C has returned) or in a `tactic`'s
`by` block:

- The arguments name the held instance up to equality by current facts:
  under `requires p == q;`, `unfold(cell(q))` opens a held `cell(p)`.
  `unfold(name)` on an instance binding opens that exact instance.
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
- A predicate: `unfold(predicate(args))` with explicit arguments.

**Failure, checking, and tools:**

An unknown or absent resource, bodyless definition, or undecided guard fails. A
trailing `unfold(resource) as { ... }` map is refused with the `let` form to
write. Click opens exactly one resource layer; expansion is unchanged, and
profiling charges the produced body.

**Checked examples:** [`composite_resource_composes_token.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_composes_token.md), [`unfold_names_its_pieces_on_the_left.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_names_its_pieces_on_the_left.md), [`conditional_resource_unfold_requires_decided_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/conditional_resource_unfold_requires_decided_guard.md), [`composite_resource_once_flag.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_once_flag.md)

### Releasing a view

`release_view(*p);` gives up a directly held memory view produced by a
call. Write the whole range held by the view. If this ends the borrow,
write access the caller lent becomes available again. The tactic runs at
the current C frontier without advancing it. See
[Producing a view](../../concepts/resources.md#producing-a-view).

### Folding resources

**Form:** `fold(resource)`

**Core.** Check the current pure body facts without searching the proof context,
consume the contained resource facts, and produce the named composite resource.
Pure facts remain available. Refolding the same instance reuses its opening's
`let ... where` witness values and checks their facts at the current state.
This also applies to the closing fold of a `with` block.
`fold(r)` supplies the exact children retained from `unfold(r)`. Each must
be held in folded form when the parent is restored. To supply a replacement,
use the explicit construction map and name the replacement in its slot.
Folding a definition whose body views memory makes
the head hold that borrow open until the head is unfolded or consumed. At a
function outcome, `fold` also [creates an ordinary abstract
token](#folding-abstract-tokens) with a matching `constructs` clause.

For an `authorized` family it creates one member and requires that family's
owned `authority(...)`; `fold(authority(R(..)))` establishes an empty
population. `let name = fold(resource, { field: value, slot: child })`
constructs an instance from one input map. The resource declaration tells Click
which entries are field values and which name held child instances. Entries
can be written in either order. Include every named child of the selected
arm, even when the held instance has the same name as the slot. An empty
input map is optional.

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
  implicit `close()`. An already-known fact is still an obligation.

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
- Inside `have ... by { ... }` or another fixed-state proposition proof: fold
  at the frontier before the `have`.

**Failure, checking, and tools:**

Every body fact is an obligation, including exactly available and trivially
true facts. The driver uses its written proof or ordinary `close()`, and
expansion retains that proof. A failed proof names the body fact.

A body fact over a witness the proof cannot name cannot be written as a
requirement, so the fold is refused at it; the fold never searches. A missing
body member, false body fact, or undecided guard fails. A child binding must
refer to an owned, folded resource of the slot's family.

Expansion prints a single input map and retains any
proofs of body facts. Profiling charges the resource body.

**Checked examples:** [`composite_resource_composes_token.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_composes_token.md), [`a_fold_binds_same_named_children_explicitly.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_binds_same_named_children_explicitly.md), [`a_fold_rejects_an_unfolded_child.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_rejects_an_unfolded_child.md), [`a_fold_requires_an_explicit_same_named_child.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_requires_an_explicit_same_named_child.md), [`fold_proves_an_unstated_body_fact_by_implicit_solve.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_proves_an_unstated_body_fact_by_implicit_solve.md), [`a_block_bound_instance_name_ends_with_its_block.md`](https://github.com/clicklang/click/blob/master/mdtests/a_block_bound_instance_name_ends_with_its_block.md), [`an_instance_bound_before_a_block_is_named_inside_it.md`](https://github.com/clicklang/click/blob/master/mdtests/an_instance_bound_before_a_block_is_named_inside_it.md)

### Folding with one obligation

**Form:** `fold(...) by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
an open body fact a different proof than the implicit closer. Any `fold` form
followed by the proof of its one body fact, written as
the resource's body fact over the fold's arguments and proved at the fold, as a
`have` would.

The body is one tactic call, such as `close();`, or a block.

**Failure, checking, and tools:**

Refused when the selected body has no fact obligation (superfluous) or more than
one; the second refusal prints each as a `requires` entry to copy. `fold(...) by
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

### Folding abstract tokens

At a function outcome, `fold(token(args))` creates one owned token of an
ordinary `abstract resource` family. It consumes no input resource. The
function must have a `constructs` clause that denotes the same token at
that outcome, and the proof must not already hold an identical token.
Arguments that evaluate to the same terms qualify. For example,
`fold(tok(n))` matches `constructs tok(result);` on a path that returns `n`.

Proof closing supplies a missing token directly owed by an active
`produces` clause at normal return. Expansion records the checked
`fold(token(args))`. Write that step explicitly when another tactic needs
the token, for example before folding a composite that owns it.

A member of an `authorized` family uses its family's population authority
before function exit. For an ordinary token, a missing or mismatched
`constructs` clause, duplicate token, or attempt before the outcome fails.
An ordinary token fold has no body obligations.

**Checked examples:** [`contract_tests.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/contract_tests.rs), [`authority_ordinary_token_construction.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_ordinary_token_construction.md), [`authority_authorized_token_construction_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_authorized_token_construction_rejected.md)

### Indexed resource unfolding and folding

**Forms:** `unfold(resource(args)[i]);` and `fold(resource(args)[i]);`

Open the declaring resource first. Its arguments must determine the guarded
iterated clause's bounds, layout, and guard. Those coordinates select one held
clause, which supplies the memory range at the current `int32` index `i`.

- Indexed `unfold` requires `i` to be in range, its guard known true, and
  `i` known distinct from every open slot. It exposes the element as owned
  memory and records an open slot.
- Indexed `fold` requires an open slot at `i`, its guard known true, and
  direct ownership of the element's memory. A slot may have been opened by
  indexed `unfold` or by a C store that made its guard true. Folding consumes
  the direct ownership and restores the slot to the clause.

Write `at(point, resource(args))[i]` to select the clause using arguments
at a recorded program point. The index, guard, and ownership transfer use
the current state. The operation runs at an execution frontier before
function exit. Expansion retains the indexed form.

**Checked examples:** [Strided slot and saved arguments](https://github.com/clicklang/click/blob/master/mdtests/indexed_iterated_ownership.md),
[Allocation](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_allocate_one.md),
[Release](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_release_one.md).

### Whole-clause resource unfolding and folding

**Forms**

- `fold(resource(args)[..]);` forms the named resource's whole iterated clause.
  It requires ownership of the guard cells and consumes the covering memory
  range when every guard is true. When every guard is false, it forms an empty
  clause without consuming element memory. A subsequent `fold(resource(args));`
  can package the clause and the rest of the resource body.
- `unfold(resource(args)[..]);` consumes the whole iterated clause and returns
  its covering range when every guard is true, or no element memory when every
  guard is false. First open the outer resource if it is folded and restore
  any open slots with indexed `fold`.

Both forms run at an execution frontier before function exit. Write
`at(point, resource(args))[..]` to select the clause using saved arguments.
The guards and ownership transfer use the current state. Expansion retains
the whole-clause form.

For a clause over `lo..hi`, both forms require every guard to be decided the
same way. The kernel checks the guard once at an arbitrary in-range index
using available quantified facts. For example,
`forall (k: int32) { lo <= k and k < hi implies occupied[k] == 0 }`
establishes that every guard `occupied[k] == 0` holds. A fact over a wider range
or one establishing every guard false also works. State the conjoined bounds
with `have` if the available fact uses nested implications.

With true guards, the elements must tile a contiguous range. For elements
`base[s * k + a..s * k + b]`, this means `b - a == s`, yielding
`base[s * lo + a..s * hi + a]`. False guards allow gapped layouts because
there is no element memory to transfer. Mixed or unknown guards prevent
whole-clause conversion. Folding may form more than one empty fact when all
guards are false. Proofs should avoid relying on this behavior.

**Checked examples** [Whole-clause round trip](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_whole_clause.md),
[Fresh guard map](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_fold_fresh_heap_map.md),
[Unknown guards](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_rejects_whole_fold_unknown_guards.md),
[Gapped elements](https://github.com/clicklang/click/blob/master/mdtests/whole_fold_refuses_elements_that_do_not_tile_a_range.md).

### User-defined tactic calls

**Form:** `name(args, { binder: instance })`

**Specialized.** Write it to apply a `tactic` the project declares, such as a
resource reshaping lemma. Apply the user-defined tactic `name` at a running
frontier or on a finished return outcome. Bind each of its supplied
resource binders to an instance the proof holds and prove its `requires` at the
call site. The application consumes its inputs, binds its outputs under the
names of a `let { binder: name }` pattern, and adds its `ensures`.

No C runs and memory is unchanged, so every fact about a cell survives.

Argument evaluation and instantiated contract requirements are ordinary proof
obligations at the selected state before the tactic changes its resources.
Argument obligations come first. Use
`by { ... }` for one obligation or `{ requires P by ...; }` to name obligations.
Omitted proofs use implicit `close()`, and expansion retains the proofs before
the tactic's resource effects are applied.
See [the checked call examples](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_requires_obligations.md).

**Accepts** an application of a `tactic` declared earlier in the module (or
the tactic itself, for recursion), when:

- There is one argument per parameter. Use a C-valued expression over the
  current state, including `result` at a return outcome, or the literal `0`
  at a pointer parameter.
- The map names every instance binder the tactic's `consumes`, `owns`, or
  `views` clauses declare, each mapped to an instance of the binder's
  resource that the proof holds. The map is left out only when the tactic
  declares no such binder; an instance of the binder's own name is not
  picked up without it.
- Every `produces` binder is named by the `let { binder: name }` pattern,
  including when the tactic produces just one resource.
- Each instantiated `requires` is proved at the call site. A recursive
  application also requires the facts establishing its `decreases` measure's
  descent.

It consumes the mapped consumed instances, adds the produced ones under the
`let` names, and adds the `ensures` facts.

**Outside it**, with what to write instead:

- An instance an earlier step consumed, including an earlier application:
  it is gone; bind the instance that step produced.
- Inside `have ... by { ... }`: apply it in the surrounding function proof.

**Failure, checking, and tools:**

A missing requirement is refused by name, as are a map entry naming an unknown
binder, an instance of the wrong resource, or a thrown outcome. Click applies
the tactic's certified contract once. Expansion retains
the call and its obligation proofs, and profiling charges the checked
application and its proof steps.

**Checked examples:** [`user_tactic_reshapes_owned_resources.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_reshapes_owned_resources.md), [`user_tactic_application_owes_its_requirements.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_application_owes_its_requirements.md), [`user_tactic_binder_map_checks_the_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_binder_map_checks_the_resource.md), [`user_tactic_consumes_its_inputs.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_consumes_its_inputs.md), [`user_tactic_at_return.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_at_return.md), [`user_tactic_accepts_null_pointer_arguments.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_accepts_null_pointer_arguments.md), [`user_tactic_recursion_converts_a_list.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_recursion_converts_a_list.md)

### Observing resources

**Form:** `observe(resource)`. A memory operand can be a range or a resource descriptor.

For an explicitly selected memory range, `observe(p[lo..hi])` adds
`viewable(p[lo..hi])` at the current program state. The exact range must be
held as a unit owner or view. This form also works at function exit and
inside a `have` proof with a concrete program state. It performs indexed
permission lookups, without looking for a covering range or following
history. The held resources do not change.

For a fixed-size linked-pointer view, `close()` can emit this observation
directly when the range already names held storage. When the base is a
pointer read from an initializer, expansion cites its equality with the
file-qualified object, rewrites the view to that object, and observes the
exact held range.

A saved range selects the pointer value at a recorded point; its bounds are
evaluated in the surrounding state. `observe(at(point, p)[lo..hi])` establishes
current `viewable(memory(at(point, p)[lo..hi]))`. `observe(old(p)[lo..hi])` uses
the entry pointer. Both use the same exact permission lookup as a current range;
they do not search intervening writes or change the selected resource.
To take both the pointer and the bounds from one point, write
`observe(at(point, memory(p[lo..hi])))`. This selects the descriptor at
`point` and checks its permission in the current state.
See [`observe_saved_pointer_memory_range.md`](https://github.com/clicklang/click/blob/master/mdtests/observe_saved_pointer_memory_range.md)
and its [missing-permission refusal](https://github.com/clicklang/click/blob/master/mdtests/observe_saved_pointer_memory_requires_ownership.md).

This establishes live storage, not initialized contents or any stored value.
To restrict the resulting fact to a smaller range, use `separation::contains_subrange`
and `separation::viewable_restrict`. For example, see
[`observe_memory_after_store.md`](https://github.com/clicklang/click/blob/master/mdtests/observe_memory_after_store.md).
[`observe_uninitialized_memory_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/observe_uninitialized_memory_rejected.md)
checks that a subsequent `close()` still cannot establish initialization.

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

Write `observe(c)` for a named folded instance you own. Its own fields supply the
body arguments and its immediate memory permissions become read-only views
supported by the instance. `observe(at(point, c))` selects the saved instance
and requires it to still be held and folded. Use `unfold` to expose named
children, then `observe(r.child)` to observe an exposed child.

**Outside it**, with what to write instead:

- Writing the body's memory, or consuming a child: `unfold` it.
- A resource not held, including one held only inside another composite:
  `observe` the parent first, one layer per step.
- After the function exit, or inside `have ... by { ... }`: observe at the
  frontier before.

When projecting a composite body, `observe` reports an undecided guard and
names the condition to prove or refute. A known-false guard selects an empty
body and succeeds.

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
reasoning uses rules such as `close()`, `normalize`, `rewrite`, and named
theorem applications. A slow simple leaf is a Click performance bug. A
successful slow smart tactic is an expansion candidate. An unsuccessful smart
tactic has nothing to expand; decompose that proof unless its search failed to
respect its bound or expose an actionable next step.

`click audit` finds smart tactics in a project, expands each one, and verifies
the rewritten source. Its purpose is to detect missing or invalid expanded
proofs, not to promise constant total verification time as a project
grows.


## Arithmetic bridge prerequisites

`close()` carries connected machine comparisons into mathematical `Integer`
comparisons through checked standard-library theorems. When observing an
addition or subtraction requires its own definedness or no-wrap bound, a
nested search does not re-enter the same operation's bridge. Already available
prerequisites can still justify the observation; a cyclic attempt is a search
miss. No stack size or work budget is raised.

[UInt64 successor with an additional bound](https://github.com/clicklang/click/blob/master/mdtests/uint64_successor_solve_with_additional_bound.md)
checks that an extra machine bound does not make an arithmetic proof recurse
indefinitely. Its false-small-bound companion keeps an unprovable conversion
bound rejected.


## Termination checks

These checked steps run inside `termination by { ... }`, including its nested
`have` bodies. They establish ordinary propositions; `close()` then closes the
corresponding goal. See [program termination proofs](../language/index.md#program-termination-proofs).

**Accepts:** `check_termination_local("f")` names a generated function body;
`check_termination_component("f", mode)` names a generated component with
`mode` equal to `strict` or `normal`, and needs its local classifications and
lower-callee classifications as available facts. Strict mode refuses indirect
calls; normal mode uses the established callback classification when necessary.
`check_termination_callbacks()` needs strict classifications for the generated
callback targets. Each needed classification may be positive or negative.

**Guarantee:** the step publishes the corresponding checked classifications,
including negations for refused descent or dependencies. It does not search for
premises or complete the enclosing proof by itself. Work follows the named
body, generated component, or program callback obligations and produced facts;
unrelated functions and proof facts are not enumerated.

**Outside it:** these steps cannot run in an unrelated function or theorem
proof, introduce a function absent from the generated scope, or replace a
missing premise. Establish that premise in a `have` proof or use `close()` to
plan the required steps. The checked example is
`mdtests/termination_ordinary_proof_steps.md`.

### Explicit `Integer` algebra expansion

Coefficient algebra and polynomial identities selected by `close()` expand
to applications of Integer distributivity, associativity, commutativity and
sign laws, followed by explicit rewrites and `close()` additive or numeric
leaves. Calls, reads, folds, and machine observations remain opaque operands.
Polynomial discovery uses the existing tactic budget and a 4096-step output
bound; it does not run inside `close()`. Supporting library proofs use
ordinary tactics.

Nonnegative quotient shifts use `integer::nonnegative_quotient_shift`: for
`d != 0`, `1 <= d`, `0 <= x` and `0 <= k`,
`truncating_quotient(x + d*k,d) == truncating_quotient(x,d)+k`.
Automatic selection currently uses positive literal divisors and proves each
sign guard from the selected premises. Missing selected guards are refused.

Checked example: [`explicit_integer_algebra_laws.md`](https://github.com/clicklang/click/blob/master/mdtests/explicit_integer_algebra_laws.md).
