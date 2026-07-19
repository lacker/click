# Proof Tactics

Click distinguishes simple tactics from smart tactics. This distinction is a
design boundary, not a performance hint.

- A **simple tactic** performs one deterministic, bounded proof operation. It
  does not search for a sequence of other tactics.
- A **smart tactic** may search, invoke solvers, or orchestrate several proof
  operations. In principle, a successful smart tactic should be replaceable by
  a certificate made from simple tactics.

A proof script is a sequence of tactics. A **proof step** is the one atomic
operation performed by a simple tactic; a smart tactic may perform many proof
steps. A **control-flow tactic** creates subgoals or scopes in which further
tactics run.
## Simple Tactics

| Tactic | One operation |
| --- | --- |
| `step()` | Advance one small C transition when every execution prerequisite is exact or context-free; do not transport facts automatically. |
| `step using { fact P; ... }` | Advance one small C transition using only the listed exact pure facts as contextual execution premises. |
| `apply_loop_summary(loop(N))` | Apply one already verified loop summary at that loop's entry. |
| `apply_loop_summary(loop(N)) using { fact P; ... }` | Apply one verified loop summary using only the listed exact pure premises. |
| `assumption()` | Close a pure goal only when that exact fact is present. |
| `normalize()` | Close a goal by context-free computation and structural normalization. |
| `intro()` | Replace one implication goal with its consequent while assuming its antecedent, or replace one universal goal with its body. |
| `conjunction()` | Close a conjunction goal when both conjuncts are exact facts. |
| `left()` / `right()` | Close a disjunction goal from the selected exact disjunct. |
| `double_negation()` | Close `not (not P)` from the exact fact `P`. |
| `vacuous()` | Close an implication from the exact negation of its antecedent. |
| `contradiction(P)` | Close any pure goal when both `P` and `not P` are exact facts. |
| `derive(P) using { fact Q; ... }` | Check one atomic consequence `P` using exactly the listed premises and the ordinary kernel theory rules. |
| `calculate(P) using { fact Q; ... }` | Check one atomic consequence using the simplifier's deterministic equality and arithmetic theory rules. |
| `rewrite(equality)` | Rewrite the current pure goal once using an exact available equality. |
| `transport(source, target)` | Apply one certified frame-transport rule from an exact source fact to the explicitly stated target fact. |
| `apply(theorem(args))` | Instantiate one theorem, require each premise exactly or by context-free normalization, and add its conclusions. |
| `unfold(predicate)` | Unfold one explicitly named predicate in matching facts and goals. |
| `unfold(resource)` | Replace one owned composite resource element with one body layer. |
| `fold(resource)` | Require the declared pure body facts exactly, consume one immediate body layer, and produce the owned composite resource element. |
| `observe(resource)` | Project one view layer from a held composite resource element. |
| `frame()` / `frame(region)` | Check one certified write summary against the declared effect segments using exact bounds. |
| `choose(...)` | Eliminate one named existential fact using the selected binder. |
| `witness(...)` | Introduce one explicit witness for the current existential goal. |

`rewrite` currently supports int32 equalities whose left side is a variable.
The equality must already be an exact pure fact; `rewrite` does not search for
equalities or derive one by congruence.

`apply` does not ask the general proposition solver to derive theorem premises.
For example, a context containing `x > 0` does not let `apply` silently satisfy
a premise `x >= 0`. Establish `x >= 0` first, then apply the theorem. A premise
such as `0 >= 0` may be accepted directly because it normalizes to true without
using the context.

The logical introduction tactics operate only while a pure goal is active,
including inside `have ... by`. They do not search for their premises. Expanded
proofs can therefore establish required premises with earlier `have` or
`apply` tactics and then invoke exactly one logical rule.

`derive` and `calculate` make atomic theory evidence explicit. Every listed
premise must be an exact available fact, and no unlisted fact from the ambient
proof context participates. They do not introduce conjunctions, implications,
quantifiers, or case splits; use the structural logical tactics for those
rules. `normalize()` remains the tactic for a context-free atomic goal.

## Smart Tactics

| Tactic | Automation performed |
| --- | --- |
| omitted `by` / `by auto;` | Orchestrate execution and proposition proving. |
| `by simp;` / `simp()` | Use the current simplifier, equalities, bounds, and supported solver rules. |
| `by frame;` | Prove an effect claim using frame reasoning. |
| `execute_step()` | Advance one small C transition while contextually proving prerequisites and automatically transporting supported framed facts. |
| `execute_then_step()` / `execute_else_step()` | Select a requested C branch using contextual condition reasoning. |
| `execute_rest()` | Orchestrate contextual execution from the current point to function exit. |
| `execute_until(...)` | Repeatedly perform contextual execution until a selected forward program point. |
| `bounded_execute()` | Repeatedly apply contextual one-step execution until function exit or a fixed step budget. |

`simp()` remains smart even though its algorithm is deterministic: it performs
nontrivial contextual reasoning rather than one fixed kernel rule. Determinism
alone does not make a tactic simple.

Click does not yet expose a surface tactic that prints or expands a smart
tactic. Internally, every current smart tactic selects and replays a proof
plan: `simp`, the one-step execution tactics,
`execute_until`, `bounded_execute`, and `execute_rest`. The contextual
`by frame` prover is certificate-backed as well; explicit `frame()` remains the
exact simple tactic. `auto` searches only among these certificate-backed tactic
sequences and no longer proves a claim through a separate whole-function
fallback.

## Tactic Certificates

The certificate foundation is deliberately narrower than arbitrary tactic
scripts. A `TacticCertificate` wraps a tactic script only after a recursive
validator establishes that every leaf is both simple and expressible in Click
source. `have`, proof-level `if`, and `advance` may remain as control-flow
nodes, but none of their nested proof scopes may contain a smart tactic. An
omitted nested proof is treated as `auto` and is therefore rejected.

Before expansion, smart tactics may retain private replay evidence in a
`ProofReplayPlan`. Replay evidence is not a tactic and cannot be placed in a
`TacticCertificate`; expansion must lower it to surface tactics first.

C verification now records a point-aware surface replay alongside ordinary
certificate replay. `VerifiedCTheorem::expanded_proof_tactics()` returns the
surface sequence when every internal item was lowered, while
`expansion_blocker()` identifies the first unsupported item. This trace does
not participate in verification; it observes the same successful replay.
`format_tactic_certificate()` prints a validated certificate as a canonical,
parseable `by { ... }` clause. `format_proof_tactics()` first validates a raw
tactic slice, so smart tactics and private replay evidence cannot be printed
as expanded Click source.
`VerifiedCTheorem::expanded_proof_certificate()` exposes the checked artifact;
`expanded_proof_source()` validates and prints it in one call. Both report the
recorded expansion blocker instead of returning partial source.

`click-expand <sidecar.click> <function> <ensure:N|effect:N|grouped>` verifies
the sidecar, replaces exactly the selected proof with its checked expansion,
and writes the complete expanded sidecar to standard output. Source files from
`verifying` declarations are resolved relative to the sidecar.
One-step execution uses only the context premises named by its recorded
proposition derivations. Atomic comparison transport is emitted as an explicit
`transport` whose source is named at the preceding statement-entry snapshot;
both source and target are re-lowered against the certified transport before
the trace accepts them.

Kernel propositions are not printed by guessing source text. Expansion builds
a checked map from each `ClickProposition` fact or goal to its exact lowered
kernel proposition, including corresponding logical subpropositions. It may
refer only to one of these recorded spellings or to a newly synthesized
spelling that successfully lowers back to the required kernel proposition.
Because lowering is snapshot-sensitive, a recorded spelling must also be
re-lowered and checked at the exact proof point where expansion emits it.

Certificate replay starts from ordinary proof inputs and delegates each leaf to
the deterministic simple-tactic executor. Failed replay does not mutate those
inputs.

`simp` plans either a context-free `normalize` leaf or internal exact
proposition derivation. The derivation records its logical structure, including
conjunction, disjunction, implication, finite case splits, and disjunction
elimination. Its atomic leaves use bounded deterministic kernel theory checks;
replay checks the selected tree and never searches for an alternative proof.
Until that derivation is lowered to surface tactics, pure `by simp` proofs do
not expose it as a tactic certificate. A `simp()` nested in a larger execution
script is planned and replayed the same way when it runs. The stored explicit
script retains its surface spelling.

Function-level `by simp` is exactly the certificate-backed sequence
`execute_rest(); simp()`. It no longer runs a separate direct execution after
checking that sequence.

`execute_step` plans one internal certified statement transition. The
transition carries explicit proposition derivations for contextual safety
prerequisites, followed by explicit theorem-backed transports for pure facts
whose memory snapshots advance. Replay checks those derivations at the exact
symbolic path point where their premises are available; it does not rerun the
contextual search that selected them.

An exact proposition derivation lowers to `have P by { derive P using { ... } }`.
If the derivation has no contextual premises, its `have` body uses
`normalize()` instead. Every conclusion and premise must have a checked Click
spelling at that proof point.

`execute_then_step` and `execute_else_step` use the same certificate form, but
planning additionally requires the current context to select the requested
arm. Replay independently checks that the certified statement transition
enters that arm.

`execute_until` plans a finite sequence of certified statement transitions.
Crossing a verified loop uses a distinct certified loop-summary transition;
each transition records the entry of the frontier it reaches, so reaching the
requested frontier requires no separate bookkeeping tactic.

`bounded_execute` produces an explicit certificate alternative for every
explored execution path. Each alternative records its condition-path facts,
then contains only certified one-step transitions. Replay executes every
alternative and merges completed frontiers; the planner cannot commit a
partially explored branch set directly.

Surface expansion retains the corresponding proof-level `if` tree. Subsequent
surface-expressible tactics are copied into every branch leaf, because a
proof-level `if` proves the current claim independently in each branch rather
than exposing an execution join.

`execute_rest` plans certified statement transitions through a straight-line
prefix. If it reaches unresolved control flow, it finishes with the same
explicit certificate alternatives used by `bounded_execute`. Consequently,
there is no whole-function execution leaf that bypasses one-step replay.

`by frame` plans path-specific proposition derivations establishing that every
certified write and effect-summary range lies inside the declared mutable
footprint. Replay checks those derivations against the corresponding execution
path and then applies the same exact footprint rule used by `frame()`.

Surface expansion spells those path-specific bounds as `have`/`derive`
tactics, followed by `frame()` in each proof leaf. Generated signed arithmetic
comparisons are converted back to Click syntax and checked by lowering them at
the same proof point; unsupported kernel terms block expansion explicitly.

`auto` tries a finite ordered set of tactic sequences. It first uses
`execute_rest` with verified loop summaries, then falls back to
`bounded_execute`; each candidate ends with `simp` or contextual frame
planning. A candidate succeeds only through its ordinary certificate replay.

## Statement Execution

`step()` and `execute_step()` advance the same execution frontier by one small C
transition. Their proof behavior differs:

- `step()` accepts an execution prerequisite only when the exact proposition is
  already a pure fact or it normalizes to true without context. It carries old
  snapshot facts as old facts and performs no automatic frame transport. When
  the next statement is an `if`, an exact condition fact selects and enters one
  arm without executing that arm's body. At a loop head, it evaluates the
  condition once and either enters one iteration or advances past the loop.
- `step using { fact P; ... }` gives the evaluator exactly the listed pure
  facts. Every listed premise must already be an exact fact. Other pure facts
  remain in the proof context but cannot influence this execution transition.
- `apply_loop_summary(loop(N))` applies that loop's already verified abstract
  rule and advances to its exit in one transition. It does not enter or replay
  the loop body.
- Its `using { fact P; ... }` form makes contextual premises explicit in the
  same way as `step using`.
- `transport(source, target)` explicitly moves one atomic condition fact to the
  current snapshot when a certified effect fact proves that its referenced
  memory was framed.
- `execute_step()` is smart automation. It invokes contextual
  prerequisite reasoning and attempts bounded automatic transport for eligible
  atomic facts. At an `if`, it uses the same contextual reasoning to select a
  uniquely determined arm. It uses the same one-condition loop transition as
  `step()`.
- `bounded_execute()` repeatedly performs contextual one-step transitions and
  explores finite symbolic branch alternatives, subject to a fixed execution-step
  budget. It is smart orchestration over the ordinary execution frontier, not
  a separate execution semantics.

`fold(resource)` never invokes `simp`. Establish each declared body fact first,
for example with `have fact by { simp(); }`; `fold` then checks those exact facts
and consumes the immediate body resources. Likewise, explicit `frame()` does
not infer symbolic range bounds. State those bounds before calling it. The
contract shorthand `by frame;` remains the smart, contextual form.

`defined(expression)` is the surface form for a C expression's safety domain.
It expands deterministically, using the kernel C evaluator, to the finite pure
proposition under which evaluation reaches a value instead of undefined
behavior. For example, `defined(x + 1)` expands to the exact signed-addition
no-overflow fact expected by `step()`.

The intended explicit pattern is to prove or apply a theorem concluding
`defined(expression)`, then call `step()`. `execute_step()` searches for the
same prerequisite from the current context and is therefore a smart shorthand
for that longer proof.

`execute_rest()` and `execute_until(...)` are deterministic smart tactics: they
do not search for a tactic sequence, but they orchestrate multiple contextual
execution operations. They may be described internally as proof macros, but
“macro” is not a separate user-facing tactic class.

## Control-Flow Tactics

The following tactics structure a proof rather than directly applying a proof
rule:

- `have`, proof-level `if`, and `advance ... ensuring ... by` structure proof
  goals and scopes. Their nested scripts may contain simple, smart, or further
  control-flow tactics.

The Rust AST enforces this inventory through `SimpleTactic`, `SmartTactic`,
`SmartTacticKind`, `ControlFlowTactic`, and `ProofTactic::class()`. Any new
tactic must be classified explicitly.
