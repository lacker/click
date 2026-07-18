# Proof Tactics

Click distinguishes simple tactics from smart tactics. This distinction is a
design boundary, not a performance hint.

- A **simple tactic** performs one deterministic, bounded proof operation. It
  does not search for a sequence of other tactics.
- A **smart tactic** may search, invoke solvers, or orchestrate several proof
  operations. In principle, a successful smart tactic should be replaceable by
  a certificate made from simple tactics.
- A **fuzzy tactic** is a current command whose implementation still combines
  deterministic work with implicit proving or broad execution. It is supported,
  but its long-term boundary has not been made precise enough to call it simple
  or smart.

Fuzzy does not mean unsound. It marks implementation and language-design work
that remains to be split into explicit rules and optional automation. New proof
features should not add more fuzzy tactics.

## Simple Tactics

| Tactic | One operation |
| --- | --- |
| `step()` | Advance one C statement when every execution prerequisite is exact or context-free; do not transport facts automatically. |
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
| `execute_step()` | Advance one statement while contextually proving prerequisites and automatically transporting supported framed facts. |
| `execute_then_step()` / `execute_else_step()` | Select a requested C branch using contextual condition reasoning. |

`simp()` remains smart even though its algorithm is deterministic: it performs
nontrivial contextual reasoning rather than one fixed kernel rule. Determinism
alone does not make a tactic simple.

Click does not yet expose a command that expands a smart tactic into its simple
certificate. Until that exists, smart tactics remain part of stored proofs.

## Fuzzy Tactics

| Tactic | Boundary still to clarify |
| --- | --- |
| `bounded_execute()` | Combines bounded program execution with obligation handling. |
| `loop_vc(loop(N))` | Checks a collection of generated loop obligations. |

The intended cleanup direction is to identify the deterministic kernel rule or
rules inside each fuzzy command, expose those as simple tactics, and retain the
existing spelling only when useful as smart automation.

## Statement Execution

`step()` and `execute_step()` advance the same execution frontier by one C
statement. Their proof behavior differs:

- `step()` accepts an execution prerequisite only when the exact proposition is
  already a pure fact or it normalizes to true without context. It carries old
  snapshot facts as old facts and performs no automatic frame transport. When
  the next statement is an `if`, an exact condition fact selects and enters one
  arm without executing that arm's body.
- `transport(source, target)` explicitly moves one atomic condition fact to the
  current snapshot when a certified effect fact proves that its referenced
  memory was framed.
- `execute_step()` is smart automation. It invokes contextual
  prerequisite reasoning and attempts bounded automatic transport for eligible
  atomic facts. At an `if`, it uses the same contextual reasoning to select a
  uniquely determined arm.

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

## Macros And Control Flow

Some proof forms are neither individual tactics nor search:

- `execute_rest()` and `execute_until(...)` are deterministic proof macros over
  execution transitions. They perform more than O(1) work and should eventually
  be expandable into smaller execution steps.
- `have`, proof-level `if`, and `advance ... ensuring ... by` structure proof
  goals and scopes. They are proof control flow. Their nested scripts may
  contain simple, smart, fuzzy, or macro commands.

The Rust AST enforces this inventory through `SimpleTactic`, `SmartTactic`,
`SmartProofStep`, `FuzzyTactic`, `DeterministicProofMacro`,
`ProofControlFlow`, and `ProofStep::class()`. Any new proof command must be
classified explicitly.
