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
| `assumption()` | Close a pure goal only when that exact fact is present. |
| `normalize()` | Close a goal by context-free computation and structural normalization. |
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
tactic's simple certificate. The internal conversion is being introduced one
smart tactic at a time; `simp`, `execute_step`, `execute_then_step`, and
`execute_else_step` are certificate-backed. `execute_until` is also
certificate-backed.

## Tactic Certificates

The certificate foundation is deliberately narrower than arbitrary tactic
scripts. A `TacticCertificate` wraps a tactic script only after a recursive
validator establishes that every leaf is a simple tactic. `have`, proof-level
`if`, and `advance` may remain as control-flow nodes, but none of their nested
proof scopes may contain a smart tactic. An omitted nested proof is treated as
`auto` and is therefore rejected.

Certificate replay starts from ordinary proof inputs and delegates each leaf to
the deterministic simple-tactic executor. Failed replay does not mutate those
inputs.

`simp` plans either a context-free `normalize` leaf or an internal exact
proposition derivation. The derivation records its logical structure, including
conjunction, disjunction, implication, finite case splits, and disjunction
elimination. Its atomic leaves use bounded deterministic kernel theory checks;
replay checks the selected tree and never searches for an alternative proof.
Pure `by simp` proofs store this expanded certificate. A `simp()` nested in a
larger execution script is planned and replayed the same way when it runs, but
the surrounding stored script continues to contain the surface `simp()` until
the other smart tactics in that script are also migrated.

`execute_step` plans one internal certified statement transition. The
transition carries explicit proposition derivations for contextual safety
prerequisites, followed by explicit theorem-backed transports for pure facts
whose memory snapshots advance. Replay checks those derivations at the exact
symbolic path point where their premises are available; it does not rerun the
contextual search that selected them.

`execute_then_step` and `execute_else_step` use the same certificate form, but
planning additionally requires the current context to select the requested
arm. Replay independently checks that the certified statement transition
enters that arm.

`execute_until` plans a finite sequence of certified statement transitions.
Crossing a verified loop uses a distinct certified loop-summary transition;
the certificate ends with a simple execution-point record so snapshots at the
requested frontier are replayed rather than committed by the planner.

## Statement Execution

`step()` and `execute_step()` advance the same execution frontier by one small C
transition. Their proof behavior differs:

- `step()` accepts an execution prerequisite only when the exact proposition is
  already a pure fact or it normalizes to true without context. It carries old
  snapshot facts as old facts and performs no automatic frame transport. When
  the next statement is an `if`, an exact condition fact selects and enters one
  arm without executing that arm's body. At a loop head, it evaluates the
  condition once and either enters one iteration or advances past the loop.
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
