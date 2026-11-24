# Smart and simple tactics

Simple and smart tactics differ in who chooses the proof steps and where the
cost of that choice is paid.

A simple tactic requests one deterministic checked operation: apply this
theorem with these premises, unfold this definition, execute this statement, or
split this goal. The verifier checks that transition directly, without
heuristic planning, premise selection, alternative-rule search, or speculative
proof branching. The operation may consult the current proof context through
indexed lookups; `step()`, for example, checks one C transition with the whole
indexed fact and resource context available.

Simple checking must also be fast and output-sensitive. Work may scale with the
tactic's explicit input, the affected program operation, indexed access to the
current proof context, and the proof-state delta it produces. It must not scan,
compare, or copy unrelated ambient state. A slow simple tactic is a verifier
performance defect, not a candidate for further expansion.

A smart tactic is a planner. It examines the proof state and tries candidate
checked operations on persistent alternatives under deterministic work
budgets, so it can fail to find a proof that exists. That is bounded
incompleteness, not evidence that the claim is false. Every piece of smart
work expands into simple tactics:

- `close()` closes the first open goal using available facts and bounded
  rules. It first checks the whole goal through its index. An exact hit
  closes immediately and expands to `close()`.
  `close() using { P; ... }` closes it from only the listed premises, trying
  arithmetic over them before a final indexed one-theorem search; a miss
  adds arithmetic's reason. Theorem discovery infers arguments from a
  structurally matching conclusion and checks prerequisites against only the
  listed facts. Expansion writes an ordinary `apply(...)` when its
  prerequisites can replay directly, and writes selected evidence for
  applications that still need it.
  A failed discovery reports a bounded sample from candidates already examined:
  a missing listed prerequisite (instantiated with the inferred arguments), an
  argument the goal does not determine (use explicit `apply`), no conclusion
  matching the supported structural fragment, or exhausted search work. A
  structural miss does not mean that no theorem could prove the goal; discovery
  does not invent witnesses or chain applications. Successful search discards
  failed alternatives' explanations.
  Integer composition expands to ordinary `have`, theorem applications, and
  explicit normalization steps. Signed intervals, definedness, and specialized
  arithmetic likewise expand to ordinary proof steps.
- The *implicit tail* ends every proof script, including the empty script of
  an omitted proof. It runs the C that is left, splitting at each C branch the
  facts do not decide into paths that each run to function exit, then closes
  every open goal on every path with the implicit closer: direct closure, then
  bounded proof search, and on a returned path that holds the body of a resource
  the contract `produces`, a fold of that resource. It has no syntax of its
  own. The same closer proves a requirement that a bare `step()`, `fold`, or
  `apply(theorem(args))` left open, and is reported as `implicit closer`
  there. An expanded theorem application keeps any needed antecedent proof
  in a preceding `have` and checks the resulting facts directly.
- At a loop back edge, the closure of the invariant bundle runs `close()` on
  each member and expands to one `have <member> by { ... }` per member not
  already a fact.
- The searches behind elided arguments, below.

`step_until(point)` repeats `step()` up to its target, and each requirement
it crosses is proved as a bare `step()`'s is. It walks a loop the facts decide
and never splits: at a C branch the facts do not decide it is refused, naming
the proof `if` or `branch` to write there. The tactic reference classifies it
as smart. The parser refuses the removed `execute()`; write
`step_until(function.exit)` or leave the C to the implicit tail.

## Elided arguments

Every other search fills one argument that a simple tactic leaves out. A
tactic written with its argument elided is a smart site; the same tactic
with the argument written is simple:

| Elided form (smart) | Written form (simple) | What the search fills |
|---|---|---|
| `transport(P, Q)` | `transport(P, Q) using { R; ... }` | the frame evidence |

Implication application checks antecedents in scope. When the ordinary
implicit closer proves a missing one, expansion writes its `have` before
`apply(fact)`. Induction application checks the hypothesis's own premises
in scope. When transport cannot find its frame evidence, the refusal is a
**search miss**: it says "this is a search miss", names the fact it did not
find, and tells you to write it (with `have P by { ... }` first, or in the
`using` form). A search miss is never a Click bug; only the written form's
refusal is a real refusal. `click expand` writes the found argument into the
same tactic, so the expanded tactic gains its `using` list.

The kernel's condition decision (`PureFactContext::decide`) is checking, not
search: simple tactics may use it, and it is bounded per query like any other
check. A simple tactic's lookups are indexed, so its cost does not grow with
unrelated facts.

## Seeing which is which

The [tactic reference](../reference/tactics/index.md) gives every form's
class, and `click docs NAME` prints it. A [proof trace](tracing.md#reading-trace-output)
marks each step smart work produced with its origin: ``(from `implicit tail`)``
for the implicit tail's execution and its closer, ``(from `close`)`` for search inside a written `close()`, and ``(from `implicit closer`)`` for
the closer of a step's requirement. It prints a `chosen:` line with the written
form of an argument a search chose. [`click profile`](../reference/cli/profile.md) reports a smart
site, elided forms included, as `SMART`, and a written simple tactic as
`SIMPLE`.

## Search and the trust boundary

Search lives on the surface, and so does the logical proposition search
underneath the smart tactics: the recursion over a goal's connectives, the
disjunction arm choice, the assumed antecedent, the finite instantiation, and
the case split over disjunction facts. It plans; the kernel checks what it
finds. No kernel operation calls it, and a kernel operation that needs to
know whether a proposition holds either answers from an exact route — the
fact index, the frozen condition checker on a bare condition, the retained
atomic memory and resource checkers — or emits the proposition as an
obligation for an ordinary tactic to prove.

Smart search remains outside the trust boundary:

- search can advance proof state only through checked simple or structural
  operations;
- a reported success must be a completed checked proof state;
- expansion must extract an equivalent sequence of surface-level simple
  tactics and verify the rewritten source;
- a missed or exhausted budget must produce a bounded, actionable failure.

Expansion is therefore both an audit boundary and a performance operation. It
replaces avoidable planning and search with direct checking of the selected
operations. The rewritten proof still pays for parsing its explicit text and
for the unavoidable semantic work of each transition, so a tiny smart tactic
need not become measurably faster. A smart hotspot should, however, lose
approximately all cost that can conveniently be removed by making its choices
explicit; a materially slow simple leaf remains an engine bug.

Use a small smart tactic when it closes a local, routine gap. Prefer explicit
simple tactics when proof intent or performance matters. Split a difficult
goal before asking search to explore more possibilities. Don't raise limits or
reshape the verified C merely to accommodate the search heuristic.

See [Tactics](../reference/tactics/index.md) for classification and [Proof-
failure triage](proof-failure-triage.md) for the boundary between an ordinary
search miss and a tooling defect.
