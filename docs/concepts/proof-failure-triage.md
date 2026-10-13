# Triaging proof failures

Click's terminal report labels a failure as a syntax error, type error, proof
error, or internal error. A proof error means a checked proof operation could
not establish its prerequisite or goal. It does not assert that the C program
is wrong. When a simple tactic was being checked, the report names that tactic;
when the checker retained an exact unresolved condition, it prints it as
`needed:`. The focused goal and recent premises provide bounded context, not
an exhaustive list of everything derivable from the proof state.

These labels describe what the CLI observed. The rest of this guide diagnoses
why a proof error happened. A rejected proof may need an available explicit
step, expose a missing capability, or reveal a bug in a documented rule.

Parsing errors in the embedded standard library name `stdlib/prelude.click` and
the line within that file. An enclosing module-checking context names the
verification being attempted; it does not change the error's source location.

A failed proof is evidence, but it does not by itself identify a Click bug.
Classify the failure before changing the proof engine, the specification, or
the C source. This keeps ordinary proof development separate from language
gaps and tooling defects.

Click is intended to verify existing C. For C within Click's supported
semantics, do not rewrite otherwise-correct implementation code merely to make
a proof easier. Keep the original source pattern in the regression and put the
adaptation or fix in the contract, proof, language, verifier, or kernel.

Ordinary errors spell every fact, goal, rejected requirement, and evaluated
side in Click or C syntax, with Click's precedence and minimal parentheses.
A refused claim reads, for example:

```text
unclosed goal: result == 8; left side evaluated to old(g[0]) + 1, right side evaluated to 8
proof context for the goal:
  case: [0 != u]
  pure facts: [old(g[0]) < 100]
```

A value is printed in its own type: `-56` for an `int32`, `4294967240u32` for a
`uint32`, and an unsigned comparison of `int32` operands converts them,
`(uint32)n <= 1073741823u32`. Machine conversions are C casts such as
`(int32)(uint32)size`, and an overflow condition reads as `defined(a + b)` or
its negation.

A read names the memory it reads. A read of the state being reported is the
bare place (`a[m]`), a read of the function's entry memory is `old(a[m])`, and
a read at a recorded mark or program point is `at(point, a[m])`. A read of any
other memory is `at(<state A>, a[m])`, and a `where` list after the report says
which program event produced each such state, for example
`<state A> is the memory after the store to a[i]`. Two reads of one place in
two memories therefore never print alike. Different states do not by
themselves establish unequal values: the proof may establish that their reads
agree.

A value no current local holds but a local held at a point this path
recorded reads at that point: inside a loop body, after `i = i + 1`, the
value `i` had when the iteration began is `at(statement(N).entry, i)`, where
`N` is the loop's statement index, the same spelling a proof cites.

Where no source name exists, the report uses a placeholder instead of a kernel
identity: `<unnamed A>` for a value no local, parameter, read, model field or
recorded point names (a callee's result, say), and `<pointer A>` for an
address no parameter or local reaches. Placeholders share one identity within a
report and are not Click proof syntax. Facts with no Click form, such as the
memory a step may have changed or resources held together, are short descriptions
in angle brackets, in source terms: `<only p[1] changed between function entry
and here>`.

An explicitly requested `--trace-proof` keeps its typed diagnostic notation:
readable Click expressions are used there only when they preserve the checked
operands, and otherwise a memory operand prints as
`read<Bits64>(snapshot#1, pointer=value#1)`, in an added fact just as in a goal.
The width, snapshot, and address remain visible even when the source wrote only
`parent->__rb_parent_color`.

Within a trace, goals, requirements, and traced facts share names and snapshot labels. A bounded legend defines
generated addresses and snapshots, including immutable proof names, pointer-read
constructions, byte offsets, and memory constructions with their inputs. An
initial empty memory is an explicit root. Other snapshots describe a recorded
transition or an internal transformation, such as projecting a source memory
for a particular pointer read, substituting a variable, or joining branch
memories. Read projections name their source snapshot and pointer. Seeded cells
name their source and stride; call and loop effects show their write footprints
when those are specified. Recorded marks and program points appear in these
definitions when they match the snapshot.

A memory-history explanation identifies a blocking store, its snapshot, and the
checked read range and write width. Its result is retained at failure time, so
formatting does not repeat the check under a different verification context.
This diagnostic walks recorded memory history
without using the proof context's equality and ownership facts. Failure to show
separation in that walk does not mean the proof has no separating evidence.
Subsequent transitions mentioned by the explanation are memory transitions, not
necessarily C statements.

Construction records travel with snapshots across threads and are excluded from
memory equality and proof evidence. A missing record on a noninitial snapshot is
reported as an internal recording defect, not a normal unknown origin. New memory
constructors must retain their operation and inputs; snapshots changed without
updating their record must not inherit an old explanation. Referenced labels are
expanded within the report budget, with display omissions explicit. Source marks
and program points are used only for matching snapshots, never guessed from nearby
statements. These definitions describe constructions, not additional checked
equalities or a complete execution history.

Each trace addition uses `adds:` followed by the same proposition form used
for `goal:` and requirements. Typed diagnostic notation is used wherever a
source expression would hide checked identities. This includes pointer and scalar equalities,
viewability with byte extents, model/function equalities, resource containment,
validated resource-composition entries, and distinct volatile-write events.
Internal notation is not promised to be valid Click proof input. Read types,
read snapshots, arithmetic widths, and signedness remain visible. Resource
compositions list up to eight entries with ownership quantities or view access;
omitted entries and support details are explicit. A write event records an
access, not an equality about the current memory contents.

Only the new facts at each checked step are printed, not the accumulated set.

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
same value and snapshot labels as the preceding trace facts.
These details are diagnostic only and do not add equalities or change proof
checking.

## Three strikes during example development

When developing an example and Click together, repeated difficulty writing a
proof is feedback about the tool, even if every rejection is sound. Use three
substantive failed attempts at the same proof obligation as a trigger to stop
local proof tweaking and investigate the verifier or proof interface.

1. On the first failure, check the claim, assumptions, and attempted step.
2. After the second failure, run a focused trace with `click verify
   --trace-proof <PROOF>`, using `--trace-to <LINE[:COLUMN]>` when useful.
   Before another attempt, state what the failed step was expected to establish,
   what the trace shows, and how that information guides the next step. If the
   trace already explains a missing premise or incorrect step, use it to repair
   the proof; an informative trace is a successful use of the existing tool.
3. On the third, pause the example at that obligation and investigate using
   the trace. Reduce the failure and ask what would make the intended reasoning
   straightforward to express and check. Do not proceed directly to a fourth
   spelling or tactic variation. Normally bring the evidence and proposed
   response to the user at this point, rather than independently redesigning
   the tooling.

Do not conclude that repeated rejection indicates a verifier defect before
trying tracing. If the trace cannot explain the relevant comparison or why an
expected fact is unavailable, identify that missing information explicitly;
improving the trace may be the right next change. Distinguish evidence visible
in the trace from hypotheses based on source inspection or instrumentation.
A clear defect such as a crash or invalid certificate still warrants immediate
investigation; tracing is not a prerequisite for recognizing independent evidence.

Count attempts to solve the same underlying obligation, not identical command
reruns or unrelated errors elsewhere in the proof. Moving the step, renaming
values, or changing tactics does not reset the count. This is a working
heuristic, not a quota: investigate sooner when the failure already exposes a
clear defect.

The pause is mandatory; changing the verifier is not. Use the triage order
below to distinguish a mistaken claim or missing premise from poor diagnostics,
an awkward proof interface, missing functionality, or an integration bug. An
explicit proof that eventually works can still expose avoidable usability
costs. Look for a general pattern, rather than a special case for the example.

Tooling improvements require discussion and user approval before implementation.
This includes choosing new diagnostic content, trace presentation, or a proof
workflow. Reproduced bugs in existing behavior may be fixed autonomously; that
permission does not extend to unapproved tooling design changes merely because
they arose during debugging. Investigate and prepare a concrete proposal first.
If the user has already approved the specific improvement, proceed within that
scope without asking again.

Before resuming, record the obligation, attempted approaches, what the trace and
reduced case show, and the chosen response. That response may be a justified proof
correction, clearer diagnostics or documentation, a reusable lemma or tactic,
or a verifier fix with regression coverage. If the tooling problem remains
unresolved, preserve the reproduction and report the blocker under the existing
bug and issue policy. Do not weaken the claim, change otherwise-correct C,
raise budgets, or add consumer-specific recovery rules merely to get past it.

This rule applies to joint example and verifier development. It does not promise
complete automation or require ordinary users to debug the verifier. Its purpose
is to turn repeated proof-writing friction into deliberate tool improvement.

## Explain the program requirement first

Tactic source excerpts retain their location and show at most ten source lines,
with an explicit omission marker for longer bodies. Individual quoted lines
are limited to 160 characters; the failure reason remains outside the excerpt.

When adding or repairing a diagnostic, lead with the C operation or contract
clause being checked and `Requires` followed by the exact Click proposition or
resource clause that is not yet established. Use the user's source expressions
and retain the access mode (`owns` versus `views`), arguments, named resource
occurrence, and relevant snapshot. An English explanation supplements this
requirement; it must not replace it.

For example, print `Requires owns counter->value` and `Available: owns
mutex_use(&counter->mutex)`. Then explain, if helpful, that `mutex_use` does not
supply the field's ownership. For a missing equality, print `Requires
counter->value == completed`. "Resource transfer failed" names neither
obligation and is not an adequate primary explanation.

Show a bounded, relevant selection of available evidence and explain the
specific mismatch. Include the C and contract/proof locations when known;
do not invent missing locations or provenance. A refusal of a C step follows
its `C operation` line, which spells the operation as Click checked it, with
a `C statement at file:line:column` line quoting the statement as written.
The C frontend records each statement's site beside its source execution
layout, keyed by statement index, and a step names the site of the statement
it checks (`CStatementSiteScope`); a site never takes part in statement
equality, so it cannot change what a proof checks or how much work it does. Equal resource arguments do not
necessarily identify the same resource occurrence: preserve source binders such
as `g` and `next` when that distinction matters. Internal subsystem names may
supplement the explanation, but must not replace it.

A failed search means the goal is not yet proved, not that it is false or that
the required resource is absent everywhere. Distinguish a missing resource from
one still folded inside another resource or temporarily lent elsewhere when
the evidence supports that distinction. Suggestions must follow from checked
evidence; do not automatically recommend stronger preconditions or changes to C.

Do not disguise unsupported verifier operations, exhausted budgets, or internal
errors as missing program facts. In particular, an unsupported rule must not be
explained as a request to prove `false = true`. Say what Click cannot yet check
and distinguish that limitation from evidence of a program bug. The
[concurrency contract proposal](../internals/concurrency-contracts-and-diagnostics.md)
contains concrete examples of the intended explanations; it is a design target,
not a claim that all current diagnostics already meet it.

## Triage order

### 1. check the claim and its assumptions

First ask whether the property is true on every execution admitted by the
contract and Click's C semantics. Look for a false postcondition, a missing
precondition, undefined behavior, an invalid loop invariant, or an effect that
the contract failed to describe.

If the claim is false or its required assumption was never declared, repair
the specification or proof. That is ordinary proof development, not a Click
issue. Do not add a precondition merely because it makes automation succeed;
the precondition must describe a real requirement of the C operation.

### 2. check the supported-semantics boundary

Determine whether the C construct and the desired property are within Click's
documented semantics. A deliberately unsupported construct is a current
limitation. If supporting it is part of Click's intended scope, record it as
**missing functionality** rather than treating the program as erroneous.

A semantics-preserving translation into Click's documented supported C may be
useful while support is incomplete, but it must be identified as such. It is
not evidence that Click verifies the unchanged source form.

### 3. replace broad search with explicit proof steps

Smart tactics are bounded, incomplete heuristics. A prompt and actionable
failure from `auto`, `execute()`, `simp()`, or another smart tactic
does not establish an engine bug. Split the task into smaller searches or use
simple tactics with explicit premises.

When `simp()` needs to reconstruct a premise at an execution snapshot, its
automatic fallback probes at most 256 statement-entry snapshots nearest the
current anchor. A missing spelling therefore cannot trigger a scan of the
whole execution history. Name a relevant older snapshot with `at(...)`, or
provide a small `using { ... }` list, when this bounded search misses. Each
candidate still has to lower to the exact retained kernel fact.
The automatic atomic fallback also declines components with more than 64
premises before rendering them; it first tries the derivation's recorded path.
This limit does not restrict an explicit `using` list. A refused written view
`simp()` retains the failing construction stage, including the actual selected
premise count when it exceeds this limit, in the ordinary error and trace.
The native kernel view query and source-certificate construction are distinct:
a positive kernel query can still lack a printable checked proof. Do not infer
a missing extent premise from that construction failure.

The result distinguishes three important cases:

- If an explicit proof works, the smart tactic's miss is at most an
  **ergonomic or automation problem**. Improve it only when there is a useful
  general pattern; do not retune shared heuristics just to make one broad
  search pass.
- If the needed valid reasoning cannot be expressed through Click's proof
  language or contracts, the failure is **missing functionality**.
- If an existing, documented proof operation applies but Click rejects it or
  gives it the wrong meaning, the failure is a **correctness bug**.

These labels describe the boundary that needs work. An ergonomic problem can
later justify a language feature, and investigation of an apparent missing
operation can reveal a correctness bug in an existing one.

### 4. separate tooling reliability from proof search

Some behavior is a tooling defect regardless of whether the underlying claim
is easy to prove. Treat the failure as a high-priority **tooling reliability
bug** when:

- a tactic exceeds its enforced class budget instead of failing promptly;
- smart search reports success but cannot advance through checked proof
  operations;
- `click verify`, `click profile`, `click expand`, and `click audit` disagree;
- expansion emits an unverifiable rewrite or operates on a failing proof;
- a normal error produces an enormous or misleading internal-state dump; or
- an interrupted command leaves verifier processes running.

Stop affected feature or example work and reduce this problem first. Do not
hide it by raising limits, adding arbitrary search caps, weakening the example,
or inserting irrelevant proof bookkeeping. See
[Performance Tools](performance-tools.md) and
[Testing Click](../internals/testing.md) for the operational workflow.

## Reading a step failure's location

Structured proof failures retain the claim, stage, source location, focused
kernel goal, and a newest-first suffix of recent premises. The original
reason remains the first line. Context is rendered only when the terminal
message is requested, with a 64 KiB report cap, bounded proposition printer,
and at most eight premises. Individual premise renderings are capped at 2 KiB
and reports say when additional context was omitted. In an ordinary report a
memory with no source name is labeled `<state A>`, `<state B>`, and so on, and
in a trace `snapshot#1`, `snapshot#2`, numbered by first appearance within one
report: equal memory shares one label and memory that differs gets another, so
"same memory" and "different memory" are visible as such. The structural
comparison stops after the first 32 distinct snapshots. Expanded
trace facts retain further snapshot identities with constant-time lookup;
repeated uses of a retained version share a label. Beyond that comparison
budget, separately constructed equal memories may receive different labels.
The legend states this distinction, and the report still has fixed output and
identity-count budgets. Diagnostic labels are context, not proof
certificates. Search
context covers bounded recent representatives from loop, induction,
refinement, and common postcondition searches; it is not a complete theorem
reasoning trace. This keeps failures useful for triage without dumping
persistent proof history or repeated raw memory snapshots.

A refused resource fold reports the instantiated body fact it could not
establish, not only its ordinal in the resource declaration. If evaluation
of the fact needs an unproved prerequisite, the error reports that specific
prerequisite instead. Ordinary errors use source spelling where available,
or show an explicitly labeled declaration when the instantiated fact cannot
be rendered in source form. `--trace-proof` also prints the exact checked proposition with typed reads
and the report's shared snapshot labels. This is the rejected requirement,
not a guessed comparison with a nearby premise. Reading it alongside accepted
trace facts can reveal a difference in values or snapshots without instrumenting
the verifier.

A failing proof step names where it was written:

```text
`allocated_vector_push.contract` proof step source tactic 1 > have body tactic 2: ...
```

`source tactic 1` is the claim's source tactic occurrence, numbered exactly as
`click expand` and `click profile` address it, so the same number selects the
tactic for expansion. Each further segment descends into a block the user
wrote: `have body tactic 2` is the second tactic of that `have`'s `by { ... }`
block, and `open body tactic 2` is the second tactic of an `open` body. Inside
a block, the arms of a proof `if`, `cases`, or `both` are blocks of their own:
`else arm tactic 1` is the first tactic of the `if`'s `else` arm (`then`,
`else`, `left`, and `right` name the arms), so a tactic written after the
`if` keeps its own position in the enclosing block even though each arm
checks it. A
failure whose driver attributed no source occurrence — a planner-generated or
searched script — reports `checked step N` instead, counting the checked steps
of the block it is proving. Do not bisect a long proof with sentinel steps
before reading this location.

## Classifying smart versus simple tactics

Classify tactics by whether they select or plan proof operations, not by whether
the user listed every contextual input. A tactic that receives hints and
chooses among normalization, rewriting, arithmetic, transport, framing, or
other theories is smart and must expand. A simple tactic checks one selected
operation deterministically, with work proportional to its relevant input,
affected program operation, indexed context access, and proof-state delta.
Simple checking must not fall through alternate strategies, search ambient
history, or scan unrelated state; if expansion cannot express the selected
operation, that is an expansion-language issue.

## Classification summary

Use the narrowest description supported by the evidence:

- **Ordinary proof development:** the claim is false, the contract is
  insufficient, or the proof has not yet supplied available reasoning.
- **Documented limitation:** the source or property is intentionally outside
  the currently supported scope.
- **Ergonomic or automation problem:** an explicit supported proof works, but
  a smart tactic misses a general case it would be useful to handle.
- **Missing functionality:** the true in-scope proof needs a fact, contract
  form, semantic rule, or simple tactic that Click cannot express.
- **Correctness bug:** an existing supported rule, semantic model, or proof
  operation rejects a valid use or accepts an invalid one.
- **Tooling reliability bug:** budgets, diagnostics, checked transitions, or
  the profile/expand/audit workflow violates its guarantees.

When evidence is incomplete, say what is known instead of guessing a label.
For example: "smart `simp()` failed; explicit resource transport has not yet
been attempted." The next experiment should be the smallest one that
distinguishes the remaining categories.

## What to put in an issue

An issue should preserve enough information to test the classification:

- a minimal regression containing the original C pattern;
- the contract and property being proved, including why the claim is true;
- the smallest explicit proof attempted and the exact point where it stops;
- the expected category and the evidence for it;
- whether verification, expansion, rewritten-source verification, and audit
  agree;
- timing and diagnostic behavior when tooling reliability is involved; and
- concrete acceptance criteria.

Do not leave the only reproduction inside a large example or an uncommitted
worktree. If reduction changes the source pattern that caused the failure, it
is not yet an adequate regression.

An explicit `apply(...)` inside `open(...)` reports an unavailable theorem
premise through the same checker used outside the scope. A `have f by simp`
that cannot establish its fact reports `Requires f`; neither refusal means
that resource scopes themselves are unsupported.
