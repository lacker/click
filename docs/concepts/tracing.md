# Repairing a failed proof

This page is the procedure for repairing a failed proof from its diagnostic
and `--trace-proof` output: find the goal that could not be proved, prove it
through explicit intermediate goals, and stop at a named outcome. It
replaces trial-and-error tactic variation with a decomposition that each
attempt must advance.

[Proof-failure triage](proof-failure-triage.md) classifies a failure once it
is understood. This page is how you come to understand it.

## Classify the verification outcome

Start with the [terminal heading](../reference/cli/verify.md#output-and-exit-behavior).

| Error kind | What it means | What to do |
| --- | --- | --- |
| `syntax error` | The sidecar does not parse. | Fix the source at the reported line. |
| `type error` | The sidecar parses but does not elaborate. | Fix the named declaration. |
| `unsupported` | Click detected a documented limitation. | Use a supported route that preserves the claim, or request support for the original case. |
| `internal error` | Click detected its own failure. | Stop at [`internal-error`](#outcomes) and capture the command, version, output, and inputs. |
| `work limit reached` | The run exhausted the overall `--work-limit`. | Record the limit and the operation that reached it. Profile the run if the work is unexpected. |
| `timed out` | Wall-clock crash containment stopped the run before a verdict. | Record the time limit and reported phase. If Click was hung, follow the procedure below. |
| `contract error` | Click identified a rule it believes a written contract clause violates. | Check the rule under the contract’s requirements. Correct the clause or report a supported `contract-bug`. |
| `tactic error` | A written tactic or implicit proof step was refused. | Check `click docs TACTIC` and establish any evidence the operation requires at that program point. |
| `unsuccessful search` | An explicit or implicit proof search found no proof. | Record the goal and write smaller proof links or supply explicit premises. |
| `incomplete proof` | The proof ended with a requirement outstanding. | Establish the named requirement before closing, such as a resource promised on return. |

When a proposition had to be true at a point and Click did not prove it,
the report prints it on a `goal:` line. That goal can come from an `ensures`
clause, a written `have`, a call's precondition, a definedness requirement such
as the absence of signed overflow, or a memory access. The report prints it on
a `goal:` line. Whatever its source, a goal is proved the same way: by the implicit tail when
the proof is omitted or the script leaves the goal open, by the implicit closer
(reported as `implicit closer`) when a `step()` or `fold` leaves a requirement
open, or by explicit tactics you write.

A goal is read in the state where it is required. A requirement of a C
statement is a goal at that statement's pre-state, so an explicit proof can
prove it just before the statement, with a `have` or a step's `requires`
entry.

## Crashes and hangs

Two failures are defects in Click whatever the proof says, and end the
procedure as soon as they happen:

| Failure | What it is |
| --- | --- |
| `crash` | Click exits without a report: a panic, an abort, a stack overflow, or the process being killed. |
| `hang` | Click runs for a long time without returning. Treat a run with no output for minutes as a hang. A timeout can also result from CPU starvation, so check whether the run was making progress. |

Do not change the proof, raise a limit, or retry to get past either one.
[Report it](#reporting-a-bug) with the exact command, the `click --version`
output, the complete output (for a hang, how long it ran before you stopped
it), and the files needed to rerun it. Shrinking them helps, but the report
need not wait for it.

## Getting a trace

Read the ordinary report first. It gives the goal, the branch facts, and the
failing tactic. When the goal alone does not explain the failure, rerun the
command the report prints under `To get a trace:`:

```text
click verify --trace-proof PROOF SIDECAR
click verify --trace-proof PROOF --trace-to LINE SIDECAR
```

`PROOF` is the function, theorem, or tactic name, and `SIDECAR` is the
`.click` file. `--trace-to LINE` stops at the written tactic on that line, even
in a proof that succeeds; use it to see the facts available at a point where
you intend to write a `have`.

The trace lists each checked step on the failing path and the facts it added
(`adds:`), then a `proof refusal` section with the goal, the resources held,
and the available premises. Those premises are what an explicit proof of the
goal can use. [Reading trace output](#reading-trace-output) describes the
notation.

A structural join is marked `(joined)`. After a source `branch` joins, only
facts established in both arms are available. A failed back-edge obligation
there names the branch, not an arm's successful last step. Use
`branch ensuring { ... }` to carry a shared fact across the join, or a proof
`if` to keep the cases apart. A trace targeted inside an arm still shows that
arm and its own checked steps. When both arms end at function exit, as the
implicit tail's early `return` does, a failure on one outcome path shows the
arm that produced that path, with its steps, instead of `(joined)`.

A goal about memory, such as a `transport` target or any goal that reads
`read<...>(state#N, pointer=value#M)`, depends on what its labels denote.
Record the legend line defining each label the goal uses: two written forms of
one C address, such as a pointer local and the `g + 16 bytes` cell it was loaded
from, or a read at entry and the same read inside a loop, are often the whole
explanation.

## Identify the primitive rule

Before splitting a link, identify the inference that should justify it. A
single proof step has specified premises, a specified conclusion, and a
checked rule connecting them. Counting tactic calls is insufficient: one
`transport ... using` can still hide a history walk. Conversely, an explicit
certificate may contain several primitive steps.

Use this map to find the applicable rule, then read its full **Accepts** list
and checked examples. The linked tactic reference is the catalog of supported
forms; this map groups them by the argument they express, not by a promise
that every current implementation meets the checking-cost contract.

| Argument needed | Rule reference | Explicit input to identify |
| --- | --- | --- |
| Reuse a fact or select a conjunct | [Available facts](../reference/tactics/index.md#available-facts), [intermediate facts](../reference/tactics/index.md#intermediate-facts) | The available proposition and selected component |
| Introduce an assumption or binder, split cases, or instantiate a universal fact | [Introducing a binder or premise](../reference/tactics/index.md#introducing-a-binder-or-premise), [explicit cases](../reference/tactics/index.md#explicit-cases), [instantiation with selected premises](../reference/tactics/index.md#universal-instantiation) | The connective or quantified fact, witnesses, and branch obligations |
| Replace an equal term | [Rewriting](../reference/tactics/index.md#rewriting) | The equality, direction, and expression being rewritten |
| Evaluate a definition or computation | [Unfolding pure functions](../reference/tactics/index.md#unfolding-pure-functions), [context-free normalization](../reference/tactics/index.md#context-free-normalization) | The named definition/application or explicit expression |
| Apply a mathematical or separation law | [Theorem application](../reference/tactics/index.md#theorem-application), [library laws](../reference/library/index.md) | The named theorem, typed arguments, and each instantiated requirement |
| Establish arithmetic | [Ordinary arithmetic proofs](../reference/tactics/index.md#ordinary-arithmetic-proofs) | Named laws, cited premises, and explicit intermediate facts |
| Execute one program statement | [Single statements](../reference/tactics/index.md#single-statements), [one statement obligation](../reference/tactics/index.md#one-statement-obligation) | The statement, its preconditions, and resulting state/effect |
| Preserve a fact across a state transition | [Preservation](../reference/tactics/index.md#preservation), [Transport with selected premises](../reference/tactics/index.md#transport-with-selected-premises) | The source fact, before/after states, checked effect, and separation or other frame premises |
| Establish current live storage | [Observing resources](../reference/tactics/index.md#observing-resources) | One exact held memory range, named by `observe(p[lo..hi])`; this establishes liveness, not initialization or a stored value |
| Manipulate ownership or open a resource definition | [Scoped resource opening](../reference/tactics/index.md#scoped-resource-opening), [tactic reference](../reference/tactics/index.md) | The selected resource instance, its definition, and required ownership quantities |

When adding a primitive, document its premises, conclusion, explicit Click
form, supported types and states, and checking-cost bound in its reference
entry. Include a passing example and controls for invalid premises, and
expansion/replay coverage when search can produce the step. A tactic name
without this rule contract is not enough guidance for proof repair.

Do not invent a library law because its mathematical statement seems familiar.
Find the declaration or documented kernel rule, instantiate its premises, and
say which premise is missing. If the premises and conclusion are expressible
and the inference is sound, but no supported primitive expresses it, stop at
`missing-rule`. Give that inference for design discussion instead of repeatedly
changing tactics or demanding intermediate facts with no rule to connect them.
If a documented rule already covers the link and refuses it, use
`tactic-bug` instead. If the mathematics itself is not established, use
`unclear-goal`; a failed search alone is not evidence of a missing rule.

### One-step preservation must be fast

Write `preserve(B, region);` under a read-equality goal.
It establishes the after-to-before read equality. The execution-produced
footprint includes writes, call effects and allocation release. Establish its
separation with explicitly supplied evidence. When a checked call publishes
`contains(R, region.footprint)`, select it with `close()` and apply the
named `separation::separate_restrict` law; `contains_refl` supplies reflexivity and
`separate_star` combines separation of several input resources. This route
does not unfold recursive resources or normalize a footprint. The older
memory-range route uses `normalize() using` with listed separations and bounds.
For a region containing several transitions, write the individual preservation
steps and compose their equalities: simple normalization does not walk a region.
The observation rule covers complete pointer, byte, 32/64-bit integer and abstract
typed cells, plus explicitly selected fields of named owned resources. For a
resource field, separate the footprint from the instance and write the field
equality across the exact entry/exit states; no unfolding or field search is
part of this primitive.
Use the [preservation reference](../reference/tactics/index.md#preservation)
for exact syntax and current producer/observation limits.

The required primitive for one recorded transition has this logical shape:

```text
observe(before, B, selector) = value
checked region before -> after has effect footprint A
separate(A, B)
-----------------------------------------------------
observe(after, B, selector) = value
```

Here B supports the complete selected observation (a typed memory cell or a
named resource field), and the source observation is valid. The effect
must include invalidation and allocation lifetime changes, as well as ordinary
writes. The transition/effect comes from checked execution;
separation comes from an explicit proof. Neither is an assumption the user may
invent. Its cost must be proportional to the selected read, supplied premises,
and explicit transition effect, up to indexing factors, independent of the
history before `before`. A large explicit effect may require proportional work.

“One step” here means one checked program transition, not one internal memory
construction. Caching a read, forgetting cached cells, or retaining an older
read origin must not make the author prove a chain of bookkeeping equalities
or make the checker search that chain. The value supplied from the preceding
step and the separation premise must suffice for this primitive.

This is a checking design requirement, not a claim that current `transport`
already implements it for every read kind. Separate a failure to express the
rule, a refusal of a documented rule, and a successful check that still walks
history. For the last case, retain a deterministic scaling reproduction as
required by [verifier design](../internals/verifier-design.md); proof success
alone does not meet the cost requirement.

Test the one-step bound by growing the preceding history while holding the
last store, read, and supplied premises fixed. Check pointer-valued as well as
scalar reads, and reject a store that overlaps the read. This measures the
primitive rather than merely demonstrating a short successful proof.

For a multi-step transport, discovering the intermediate transitions or
premises may be search. Its expansion must name the transitions and premises
used by the primitive applications, so replay costs roughly the written proof
size and does not rediscover history. An explicit `using` list only selects
premises; it does not by itself certify that checking is fast.

## The procedure

Start with the [verification outcome](#classify-the-verification-outcome).
Use `unclear-output` when the available diagnostics lack the detail
needed to tell whether the proof author or Click maintainers should follow up. For example, a contract error may omit
the clause or rule to check, or an implicit-step refusal may omit the
operation Click tried. When a proof obligation is outstanding, work from
that obligation.

1. **Record the goal.** Write down the failing goal `G`, the point
   where it is required, and the premises available there. Read the diagnostic
   and any available trace. A named resource and return path can identify
   a requirement. If you still cannot identify the requirement or its point,
   stop at `unclear-output`.
2. **Decide whether `G` is true.** Check it against the contract, the branch
   facts, and the C semantics. If an admitted execution refutes `G`, check
   the original claim on that execution and the rule that introduced `G`.
   Use `false-claim` if the execution refutes the original claim. Use
   `obligation-bug` if Click generated `G` without support from the
   applicable semantics or documented rule. Revise a stronger intermediate
   goal that the proof author chose and the argument does not need.
3. **Write the argument.** State why `G` follows from the premises as a chain
   of intermediate facts: the premises imply `A`, `A` implies `B`, and `B`
   implies `G`. Write each link as a `have` at that point, so the proof
   checks it. If you cannot state the argument, stop at `unclear-goal`. If you
   cannot write one of the intermediate facts in Click, stop at
   `inexpressible-fact`.
4. **Run it.** The first link that fails is the new `G`. Return to step 1 with
   it.
5. **Refine a link that does not close.** Identify its primitive rule using
   the map above. If the argument needs several rules, split it into links
   with those rules as endpoints and run again. A failed smart tactic does
   not establish whether a link is primitive. Stop splitting when all the
   premises for a documented primitive are written, or when a concrete sound
   inference has no supported primitive (`missing-rule`). Do not classify a
   link as primitive solely because it is one tactic call.
   The [tactic table](../reference/tactics/index.md) gives each tactic's class,
   and `click docs NAME` prints its forms and documented behavior. A refusal
   may identify the tactic with `refused by:`. An `incomplete proof` names
   the requirement still outstanding when the proof closes. If a written primitive is refused
   within its documented **Accepts** list, stop at `tactic-bug`.

   To split a link that a smart tactic proved part of, read its trace: a step
   marked ``(from `implicit tail`)``, ``(from `close`)`` or
   ``(from `implicit closer`)`` is one that smart work took, and a `chosen:`
   line is the written form of an argument its search chose ([Reading trace
   output](#reading-trace-output)). Writing those out leaves only the
   unproved part of the link.
6. **On a search miss, write the argument.** An elided form, such as
   `apply(t(x))` or a bare `transport(P, Q)`, searches for an argument that
   a simple form of the same tactic takes written. When the search finds
   nothing, the heading is `unsuccessful search` and the report may name the
   tactic on a `refused by:` line. State the missing fact with `have`
   first, or write the `using` form, and run again. Only the written form's
   refusal can be `tactic-bug`.

Before each run, say in one line which link is new and why it should hold.
Changing a tactic, its written form, or its position without changing the chain
is not a new attempt. Do not edit `close()` or the implicit closer, raise a
budget, or change the C to get past a link.

Before reporting a refused simple link, shrink the link itself, not only the
program around it. Drop each `using` premise, alias, and earlier `have` it does
not need while the refusal stays; write it with the C local the statement uses
rather than a spec alias; and find the nearest link that passes, such as the
same transport of another field across the same store, noting what differs
(the field's type and width, its offset, how the address is written). Then
compare the refusal with the one-line argument and name the step Click did not
take: which addresses it did not identify, which read it did not carry, which
fact it did not read.

## Outcomes

The procedure ends at exactly one of these:

| Outcome | Meaning |
| --- | --- |
| `success` | The proof verifies. Keep the explicit links that the default automation needed; they document the argument. |
| `false-claim` | An execution admitted by the contract violates the original claim. Give the counterexample so the proof author can revisit the claim, contract, or program. |
| `obligation-bug` | Click generated a requirement unsupported by the applicable semantics or documented rule. Give the discrepancy so Click maintainers can investigate obligation generation. |
| `unclear-goal` | You can read `G` and its premises, but have neither a justification nor a counterexample. Say why you expected the proof to work and identify the local gap in the argument. |
| `missing-rule` | The premises and conclusion are expressible and the inference is justified, but no supported primitive connects them. Record the rule schema, the references checked, and the reduced example for design discussion. This is not established by a search miss alone. |
| `inexpressible-fact` | The argument needs an intermediate fact Click cannot write, such as a missing predicate, quantifier form, memory syntax, or resource form. Report a bug. |
| `contract-bug` | Click refuses a contract that satisfies the documented rule. Quote the clause and exact refusal and show how the contract satisfies the rule. Click maintainers follow up. |
| `tactic-bug` | Click refuses a minimized simple tactic whose written premises justify its goal and whose documented **Accepts** list covers the link. Report a Click bug. |
| `unclear-output` | The available diagnostics leave responsibility undetermined. Quote the output and name the missing or ambiguous detail that prevented triage. |
| `work-limit-reached` | Click exhausted the entire run’s `--work-limit`. Report the budget and the operation where it stopped. |
| `timed-out` | The wall-clock containment bound stopped Click before a verdict. Report the bound and the last reported operation, if available. |
| `internal-error` | Click printed `internal error`. Tell the user immediately that Click detected a verifier failure. A proof goal or a minimized tactic link is optional evidence. |

The `proof refusal:` heading locates a refusal. The outcome depends on what
the proof-repair investigation establishes. For a smart-tactic miss or a
failed search for an omitted argument, identify the primitive and state
its premises. Report diagnosis as in progress while checking the inference
and its documented support. File a diagnostic bug from `unclear-output`
only when you can demonstrate a specific defect in the output.

### Reporting a bug

Report a Click defect with the user's approval as an issue at
<https://github.com/clicklang/click/issues> that contains enough to reproduce
it. Label the issue with its outcome (`tracing: inexpressible-fact`,
`tracing: contract-bug`, `tracing: obligation-bug`, `tracing: tactic-bug`, `tracing: unclear-output`,
`tracing: internal-error`, `crash`, or `hang`), and
start its title with it in brackets (`[tactic-bug] ...`, `[hang] ...`) so
it shows even without permission to set labels.

For `internal-error`, include the exact command, the `click --version` output,
the full diagnostic, and the inputs needed to reproduce it. For a crash or
hang, follow [Crashes and hangs](#crashes-and-hangs).

For `contract-bug`, include the reduced inputs, the exact command,
`click --version`, and the complete diagnostic. Identify the clause, cite
the contract rule, and show how the original contract satisfies it under
its stated requirements.

For `obligation-bug`, include a reduced reproduction, the original claim,
the generated goal at its program point, and the exact command and output.
Cite the rule or semantics that governs the check and show what it actually
requires. Include any execution that satisfies the claim while refuting the
generated goal.

For a confirmed diagnostic defect found during `unclear-output` triage,
include the reduced inputs, exact command, `click --version`, and complete
output. Identify the missing or misleading detail and show the evidence for
the discrepancy. Include any trace or goal that helps demonstrate it.

For `tactic-bug` or `inexpressible-fact`, include:

- the smallest C and Click that still fail, keeping the original source
  pattern, with the exact command and its output, including the `goal:` line;
- the chain up to the failure, with every earlier link proved;
- the failing link in its smallest form: its goal, the tactic, and the
  refusal, with the legend line for every label the goal uses;
- the nearest passing link and what differs from it;
- why the link holds, in one line of mathematics, and the step of that
  argument Click did not take; and
- for `tactic-bug`, the item of that tactic's **Accepts** list that
  covers the link.

## Worked example

`frame` returns one more than the product its callee computes:

<!-- verified-example: mdtests/tracing_a_nonlinear_bound_is_the_refused_goal.md -->
```c
int area(int w, int h) { return w * h; }
int frame(int w, int h) {
    int inner = area(w, h);
    return inner + 1;
}
```

<!-- verified-example: mdtests/tracing_a_nonlinear_bound_is_the_refused_goal.md -->
```click
int32 frame(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures to_integer(result) == to_integer(w * h + 1);
}
```

With `area`'s contract stating `to_integer(result) == to_integer(w * h)`
under the same bounds, the omitted proof is refused: its implicit tail steps to
the `return`, where the closer of the statement's requirements cannot prove
that the addition does not overflow. It ends with the goal and how to prove it
(abbreviated):

```text
unsuccessful search:
  `frame.ensures_0` tactic 0
  `step()` produced undefined behavior
  signed overflow
  ...
  `return inner + 1;`

tactic: step
  ...
goal: inner <= 2147483646
help: to prove the goal explicitly, step to this statement and prove it there with `have <goal> by { ... }`
```

1. **Goal.** `inner <= 2147483646` before `return inner + 1;`. The trace's
   proof refusal lists the bounds on `w` and `h`, and the call step added
   `inner == w * h`.
2. **True?** Yes: `w * h` is at most `1000 * 1000`.
3. **Argument.** `inner == w * h`, `w * h <= 1000000`, and `1000000 <=
   2147483646`. The middle link is the one the implicit closer did not
   derive, because it is nonlinear.
4. **Write it.** Step through the declaration and the call, then state the
   link:

<!-- verified-example: mdtests/tracing_an_intermediate_goal_proves_the_bound.md -->
```click
    ensures to_integer(result) == to_integer(w * h + 1) by {
        step(); step();
        have to_integer(w * h) <= 1000000 by close();
    }
```

The implicit tail runs the `return` and closes the claim. The proof verifies:
`success`. Had `have to_integer(w * h) <= 1000000 by close();` been refused, it would be the new goal, to split further, for example through
`w * h <= 1000 * h`.

## Reading trace output

An explicitly requested `--trace-proof` keeps its typed diagnostic notation:
readable Click expressions are used there only when they preserve the checked
operands, and otherwise a memory operand prints as
`read<Bits64>(state#1, pointer=value#1)`, in an added fact just as in a goal;
a read of a value of algebraic type names its type, `read<T>(..)`.
The width, memory label, and address remain visible even when the source wrote only
`parent->__rb_parent_color`.

In the failed-check section, memory ranges whose identical printed footprints
hide different pointer metadata receive shared `[range A]`, `[range B]`
labels. A range-identity legend gives their object identities and known or
opaque bounds. Comparison happens only when rendering this trace, over at most
64 distinct displayed range representations; hitting that cap is reported.
Equal ranges keep one label, and unambiguous footprints gain no annotation.
This describes a representation mismatch, not additional proof evidence.

Within a trace, goals, requirements, and traced facts share names and memory
labels. A `transport` refusal that finds no frame evidence prints its own
legend first, and the trace continues its numbering, so a label in the refusal
and in the `proof refusal` goal means the same value or memory. A field of a named pointer prints as that name
plus its byte offset (`g + 16 bytes`). A bounded legend defines
generated addresses and memory labels, including immutable proof names, pointer-read
constructions, pure pointer calls with their typed arguments, byte offsets,
and memory constructions with their inputs. Pure-call arguments retain model
identities and read memory labels; nested pointer arguments have their own legend
definitions. These constructions explain labels and add no proof evidence. An
initial empty memory is an explicit root. Other memory labels describe a recorded
transition or an internal transformation, such as projecting a source memory
for a particular pointer read, substituting a variable, or joining branch
memories. Read projections name their source memory and pointer. Seeded cells
name their source and stride; call and loop effects show their write footprints
when those are specified. Recorded marks and other points appear in these
definitions when the labeled memory is the one recorded there.

A memory-history explanation identifies a blocking store, its memory label, and the
checked read range and write width. Its result is retained at failure time, so
formatting does not repeat the check under a different verification context.
This diagnostic walks recorded memory history
without using the proof context's equality and ownership facts. Failure to show
separation in that walk does not mean the proof has no separating evidence.
Subsequent transitions mentioned by the explanation are memory transitions, not
necessarily C statements.

Construction records travel with labeled memories across threads and are excluded from
memory equality and proof evidence. A missing record on a noninitial memory is
reported as an internal recording defect, not a normal unknown origin. New memory
constructors must retain their operation and inputs; memories changed without
updating their record must not inherit an old explanation. Referenced labels are
expanded within the report budget, with display omissions explicit. Source marks
and other points are used only for memory recorded at them, never guessed from nearby
statements. These definitions describe constructions, not additional checked
equalities or a complete execution history.

Each trace addition uses `adds:` followed by the same proposition form used
for `goal:` and requirements. Typed diagnostic notation is used wherever a
source expression would hide checked identities. This includes pointer and scalar equalities,
viewability with byte spans, model/function equalities, resource containment,
validated resource-composition entries, and distinct volatile-write events.

A refused subobject access retains its bounds requirement on the `goal:`
line. Concrete bounds use byte-range containment. Opaque bounds print
`subobject bounds of P cover bytes [A, B)`: `P` identifies the pointer
whose bounds are needed, while `[A, B)` is the attempted access. This is
bounds evidence, not merely integer address equality or ownership at that address.
The refusal does not establish that the access is invalid on every execution;
it can also mean the proof has not established its bounds.

Recorded-point names for read constructions come from the exact memory-read
index, including points older than the recent trace window. These annotations
identify matching program bytes, not equality of complete memory states or
pointer bounds. A projected pointer-read description also identifies the
selected cell.

Internal notation is not promised to be valid Click proof input. Read types,
read memory labels, arithmetic widths, and signedness remain visible. Resource
compositions list up to eight entries with ownership quantities or view access;
omitted entries and support details are explicit. A write event records an
access, not an equality about the current memory contents.

Only the new facts at each checked step are printed, not the accumulated set.

A step whose store dropped a cached cell of the same array says so, with the
fact the store reads to keep it:
``forgets cached `q[0]` beside the store to `q[(m - 1)]`: the store keeps it
only on the stated fact …``. The fact is the disequality of the two `int32`
index words; state it before that statement to keep the cell. The trace reads
this from the step's own memory delta (the cells the two memories differ on,
at most four pairs listed); the store itself records nothing. A step whose
read followed memory history and stopped without reaching the value says
`read history stopped after crossing N recorded transitions (a read follows
at most one)`, with the walk's address, start and stop memories and reason:
a read follows one recorded transition, so a value an older store left needs
an explicit transport or a fact stated before the intervening statement. At
most four such walks are listed per step.

When the implicit tail's store search could not prove that disequality, a
refusal whose goal reads the dropped cell adds a line naming the statement
and the fact as the search stated it (in a trace, a `store search:` line
under the memory-history check). A proof `if` is recorded at its own line, so
`--trace-to` a tactic in either arm selects that arm.

A step that a search produced says which one. A step that smart work checked
ends its header with ``(from `implicit tail`)`` or the like, naming its
origin: `implicit tail` for the steps the implicit tail took and for its
closer, `close` for search inside a written `close()`, and
`implicit closer` for an obligation a `step()` or `fold` left open. A step
whose arguments a search chose can have a `chosen:` line with the tactic
written out as `click expand` writes it:

```text
tactic@11: apply
  chosen: apply(le_trans(x, y, z));
  adds: x <= z
```

Writing the `chosen:` form removes the search for those arguments. It does
not establish that the checked implementation avoids history walks; apply
the one-step cost requirement above separately. A step with neither mark is one the script wrote.

A failure trace also ends with a separately labelled `proof refusal`. It retains
the refusal, checking stage, proof context, up to sixteen available premises,
and up to twelve resources from the retained C state, even when the first operation fails before a checked step can
be recorded. For postcondition failures, current-state names and resources come from the
selected outcome; permissions consumed by a call are not shown as still held.
The proof refusal is not an accepted execution step. A proposition
proof has a fixed execution state; an execution tactic refused there names that
restriction rather than implying that the tactic is unavailable everywhere.
When an explicit script ends with a goal still open, its failure retains the
checked prefix and the remaining goal and premises after those steps, rather
than the state at script entry. This includes execution `have` bodies and pure
theorem scripts.

Written `close()` failures retain a bounded sample of the read-value queries and
cell walks actually performed during that attempt. Ordinary errors summarize
up to two observations of each kind and eight available premises; traces show
up to sixteen observations of each kind, with shared
memory and address labels, access widths, stopping reasons and query modes.
These records include speculative search queries and are not additional proof
facts or a claim that one observed stop explains the entire search failure.
A check with no instrumented memory query says so in its trace. The capture
limit bounds diagnostic storage and does not stop or change verification.
Supplemental memory-history explanations are labelled separately: their walk
does not use the failing check's equality or ownership context. Actual query
observations retain the context's result without rerunning it while printing.

A loop-closure search error names its unresolved obligation from the member
planner or the retained focused goal, including when that search exhausted its work budget.
If no individual obligation was retained, the diagnostic says that the failure
applies to the bundle search. A budget refusal reports an unfinished proof
attempt; it does not establish that the named obligation is false.

A failed pointer-valued resource child argument comparison reports the exact
supplied and required values and the argument position. Up to four explicit
equalities sharing the supplied value may be shown as potentially relevant
evidence. That selection is diagnostic guidance, not a claim about the cause
of failure or a prescription for the missing proof. The comparison uses the
same value and memory labels as the preceding trace facts.
These details are diagnostic only and do not add equalities or change proof
checking.
