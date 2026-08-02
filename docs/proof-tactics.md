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

This page is the complete inventory of surface tactic spellings. The
[synonyms and legacy spellings](#synonyms-and-legacy-spellings) section lists
every case where two spellings mean the same thing, and every case where two
similar-looking spellings do *not*.

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
| `transport(source, target) using { fact P; ... }` | Transport an exact atomic source to the explicitly stated target using its certified fact-family rule and execution effects, from only the listed premises. |
| `apply(theorem(args)) using { fact P; ... }` | Instantiate one theorem from exactly the listed premises and add its conclusions. |
| `close_invariants()` | Discharge a loop's whole invariant bundle at the back edge of a `preserve` proof. |
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

Neither spelling of `apply` asks the general proposition solver to derive
theorem premises. For example, a context containing `x > 0` does not let
`apply` silently satisfy a premise `x >= 0`. Establish `x >= 0` first, then
apply the theorem. A premise such as `0 >= 0` may be accepted directly because
it normalizes to true without using the context. The difference between the two
spellings is only where the premises come from: bare `apply(theorem(args))`
draws them from the ambient pure facts and is therefore smart, while
`apply(theorem(args)) using { fact P; ... }` names them and is simple.
Expansion rewrites the first into the second.

`transport` splits the same way: bare `transport(source, target)` is smart and
`transport(source, target) using { fact P; ... }` is the simple, exact-premise
form it expands to.

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
| `apply(theorem(args))` | Instantiate one theorem, drawing each premise from the ambient pure facts or context-free normalization. |
| `transport(source, target)` | Transport an exact atomic source to the stated target, selecting the premises from the ambient context. |
| `execute_step()` | Advance one small C transition while contextually proving prerequisites and automatically transporting supported framed facts. |
| `execute_then_step()` / `execute_else_step()` | Select a requested C branch using contextual condition reasoning. |
| `execute_rest()` / `symbolic_execute()` | Orchestrate contextual execution from the current point to function exit. |
| `execute_until(...)` | Repeatedly perform contextual execution until a selected forward program point. |
| `bounded_execute()` | Repeatedly apply contextual one-step execution until function exit or a fixed step budget. |

`simp()` remains smart even though its algorithm is deterministic: it performs
nontrivial contextual reasoning rather than one fixed kernel rule. Determinism
alone does not make a tactic simple.

Expansion is a command-line source transformation rather than an in-language
tactic: `click-expand` replaces one selected smart tactic with its checked
surface certificate. Internally, every current smart tactic selects and
replays a proof plan: `simp`, the one-step execution tactics,
`execute_until`, `bounded_execute`, and `execute_rest`. The contextual
`by frame` prover is certificate-backed as well; explicit `frame()` remains the
exact simple tactic. `auto` searches only among these certificate-backed tactic
sequences and no longer proves a claim through a separate whole-function
fallback.

## Control-Flow Tactics

These tactics structure a proof rather than directly applying a proof rule.
Their nested scripts may contain simple, smart, or further control-flow
tactics.

| Tactic | Structure created |
| --- | --- |
| `have proposition by ...` | A scoped pure proof whose conclusion is added to the current pure facts. |
| `if proposition { ... } else { ... }` | Two proofs of the current claim, one under the proposition and one under its negation. |
| `advance(point) ensuring { ... } by { ... }` | A scoped execution proof that must reach `point` and establish the declared interface. |

## Synonyms And Legacy Spellings

Click accumulated several spellings for the same operation. The parser
(`src/lang/click/parser.rs`) and the classifier (`ProofTactic::class()` in
`src/lang/click.rs`) are the ground truth; this table restates them.

### Spellings that mean exactly the same thing

| Canonical | Accepted synonyms | Note |
| --- | --- | --- |
| `by auto;` | omitted proof clause, `by { auto; }` | `auto` is the default prover. |
| `by simp;` | `by { simp; }` | Whole-claim smart proof. |
| `by frame;` | `by { frame; }` | Whole-claim smart effect proof. |
| `execute_rest()` | `symbolic_execute()` | Legacy spelling; both parse to the same tactic. Prefer `execute_rest()`. |

`auto` has no call spelling. Writing `auto()` inside a script is rejected with
``` `auto` is only available as a standalone smart tactic; use `by auto;` ```.
`simp` and `frame` do have call spellings, but they are *not* synonyms of the
`by` forms — see below.

### Spellings that look alike but differ

| Pair | Difference |
| --- | --- |
| `by simp;` vs `by { simp(); }` | `by simp;` is the smart whole-claim proof, exactly the sequence `execute_rest(); simp()`. `by { simp(); }` is a one-tactic script, and `simp()` requires execution to already be at function exit. |
| `by frame;` vs `frame()` | `by frame` derives the range bounds contextually (smart). `frame()` requires the bounds to be exact available facts (simple). |
| `step()` vs `execute_step()` | Both advance one C transition. `step()` needs exact or context-free prerequisites and transports nothing (simple); `execute_step()` reasons contextually and transports supported facts (smart). |
| `step()` vs `step using { fact P; ... }` | Both simple. The `using` form restricts the evaluator to exactly the listed premises. |
| `apply(t(a))` vs `apply(t(a)) using { ... }` | Bare is smart (ambient premises); `using` is simple (named premises). |
| `transport(s, t)` vs `transport(s, t) using { ... }` | Same split as `apply`. |
| `apply_loop_summary(loop(N))` vs its `using` form | Both simple; the `using` form names the contextual premises. |
| `unfold(name)` vs `unfold(resource(args))` | Predicate unfolding vs. one composite-resource body layer. The parser picks by whether the argument is a call. |
| `execute_until(...)` vs `advance(...)` | `execute_until` moves the frontier along a deterministic prefix. `advance` proves a scoped region and replaces the frontier with a declared interface. |
| `execute_rest()` vs `bounded_execute()` | `execute_rest` runs a straight-line prefix and finishes unresolved control flow with certificate alternatives. `bounded_execute` explores branch alternatives under a fixed step budget. |

### Names that are not surface spellings

`CLICK_TIMINGS=1` and certificate dumps print internal tactic names that cannot
be written in a `.click` file: `certified_statement_step`,
`certified_loop_summary_step`, `certified_fact_transport`,
`finish_certified_fact_transports`, `certified_path_assumption`,
`certified_frame`, `certified_alternatives`, and
`exact_proposition_derivation`. They are replay evidence produced by expansion,
not tactics an author writes.

## Where Each Tactic Is Available

Not every tactic is accepted in every proof position.

- **Function proofs** (per-claim `by { ... }` and the grouped trailing block)
  accept the whole inventory, except that `close_invariants()` is rejected with
  ``` `close_invariants` is only available in a loop-region proof ```, and the
  purely logical tactics (`intro`, `conjunction`, `left`, `right`,
  `double_negation`, `vacuous`, `contradiction`, `derive`, `calculate`) are
  rejected unless a pure goal is active, typically inside `have ... by`.
- **Pure theorem proofs** accept `by auto;`, `by simp;`, and scripts built from
  `unfold(predicate)`, `apply(...)` in both spellings, `assumption()`,
  `normalize()`, `intro()`, `conjunction()`, `left()`, `right()`,
  `double_negation()`, `vacuous()`, `contradiction(P)`, `derive(...)`,
  `calculate(...)`, `rewrite(...)`, `simp()`, and proof-level `if`. Everything
  else — including `by frame;`, `have`, `witness`, `choose`, `advance`, all
  execution tactics, and all resource tactics — is rejected.
- **Loop `initialize by { ... }`** is a pure proof at the actual loop entry. It
  accepts only `unfold(predicate)`, bare `apply(...)`, `have`, `assumption()`,
  `normalize()`, `rewrite(...)`, `simp()`, and proof-level `if`.
- **Loop `preserve by { ... }`** is an execution proof over one iteration. It is
  the only place `close_invariants()` is accepted.

## Closing A Loop Invariant Bundle

`close_invariants()` discharges a loop's whole invariant bundle at the back edge
of a `preserve` proof. It takes no arguments and may run at most once on a path;
a second occurrence fails with `the invariant bundle was closed more than once
on one path`.

Writing it is optional. When a `preserve` script does not close the bundle
itself, Click appends the closer implicitly after the last written tactic, and
the certificate still contains an explicit `close_invariants` leaf. Write it
explicitly when the script needs the invariant check to happen at a specific
point, or when reading an expanded proof, where it always appears.

```click
for loop(0) {
    invariant i >= 0;
    invariant i <= n;

    initialize by auto;
    preserve by {
        execute_step();
        close_invariants();
    }
}
```

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
The canonical renderer is a Surface Click renderer: retained field places print
as `owner->field`, complete struct storage prints as `object(owner)`, and an
internal kernel term is never exposed as a private textual spelling.
`VerifiedCTheorem::expanded_proof_certificate()` exposes the checked artifact;
`expanded_proof_source()` validates and prints it in one call. Both report the
recorded expansion blocker instead of returning partial source.

`click-expand <sidecar.click>:<line>:<column>` verifies the sidecar, infers the
enclosing function and proof from the one-based source location, replaces
exactly the tactic beginning there with its checked expansion, and writes the
complete expanded sidecar to standard output. Nested branch and `advance`
tactics use the same location scheme. Source files from `verifying`
declarations are resolved relative to the sidecar. An optional
`--time-limit <DURATION>` overrides the default 60-second bounded child
process.
One-step execution uses only the context premises named by its recorded
proposition derivations. Atomic comparison and structural-memory transport are
emitted as explicit `transport` steps whose sources name the relevant
historical snapshot; both source and target are re-lowered against the
certified transport before the trace accepts them.

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
- `transport(source, target)` explicitly moves one atomic fact to the current
  snapshot. Conditions require certified framing of referenced memory;
  structural facts such as `loadable(...)` are re-derived from the source and
  certified effect facts. This bare spelling is smart because it selects its
  premises from the ambient context; `transport(source, target) using
  { fact P; ... }` is the simple form it expands to.
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
“macro” is not a separate user-facing tactic class. `symbolic_execute()` is a
legacy spelling of `execute_rest()` and parses to the same tactic.

## Classification Source Of Truth

The Rust AST enforces this inventory through `SimpleTactic`, `SmartTactic`,
`SmartTacticKind`, `ControlFlowTactic`, and `ProofTactic::class()`. Any new
tactic must be classified explicitly.
