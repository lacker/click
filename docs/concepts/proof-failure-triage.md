# Triaging proof failures

Start with the [CLI outcome](../reference/cli/verify.md#output-and-exit-behavior).
For a `tactic error`, check the invocation against its documentation. For an
`unsuccessful search`, identify the goal and supply the intermediate facts
or arguments that the search did not find. For an `incomplete proof`,
establish the reported requirement before the proof closes. For a returned
resource, check what the contract promises and what the return path holds. For a `contract error`, check
whether the clause satisfies the documented rule under its requirements.
Correct an invalid clause or report `contract-bug` with evidence that the
original clause satisfies the rule. For a contract-entry, execution,
or termination refusal, inspect the specific reported check.

Use the [proof repair procedure](tracing.md) when the diagnostic gives a
goal. A statement requirement is a goal at the statement’s pre-state.
The recent premises in the ordinary report are a bounded sample.

Parsing errors in the embedded Click library name the module file, such as
`library/c/string.interface.click`, and the line within that file. An enclosing module-checking context names the
verification being attempted; it does not change the error's source location.

A failed proof is evidence, but it does not by itself identify a Click bug.
Classify the failure before changing the proof engine, the specification, or
the C source. This keeps ordinary proof development separate from language
gaps and tooling defects.

Click is intended to verify existing C. For C within Click's supported
semantics, do not rewrite otherwise-correct implementation code merely to make
a proof easier. Keep the original source pattern in the regression and put the
adaptation or fix in the contract, proof, language, verifier, or kernel.

Ordinary errors print every fact, goal, rejected requirement, and evaluated
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
`n as uint32 <= 1073741823u32`. Machine conversions are C casts such as
`size as uint32 as int32`, and an overflow condition reads as `defined(a + b)` or
its negation.

Float prerequisites retain source names and print exact IEEE bit literals,
such as `d >= float64_from_bits(0xc1e0000000000000u64)` and
`d < float64_from_bits(0x41e0000000000000u64)` for the int32 cast bounds.
These printed forms preserve the float type and can be reused as contract
prerequisites; see [exact float bit literals](../reference/language/grammar.md#exact-float-bit-literals).

A read names the memory it reads. A read of the state being reported is the
bare place (`a[m]`), a read of the function's entry memory is `old(a[m])`, and
a read at a recorded mark or other point is `at(point, a[m])`. A read whose
version point is not currently a recorded, nameable point is `at(<state A>,
a[m])`, and a `where` list after the report says which program event produced
each such state, for example
`<state A> is the memory after the store to a[i]`. Two reads of one place in
two memories therefore never print alike. Different states do not by
themselves establish unequal values: the proof may establish that their reads
agree.

When a comparison's two sides read one address in different memories, the
refusal names the memory each side's read is recorded at, from the read's own
version point or the recorded point holding its memory: the function-entry
memory, the outcome memory, or the memory recorded at a point, which for a
call's exit also names the call:

```text
unclosed goal: result == a[m]; the two sides read the same address in different memory states (`result` reads the function-entry memory; `a[m]` reads the memory recorded at `statement(3).exit`); `a[m]` may have changed since function entry: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`.
```

The resource tracker then names the step between the two reads that broke
the chain. Where it shows the cell unchanged between them, the text says
"the cell is unchanged between the two reads, but they carry different read
names": the values differ only in how the reads were named, which is a
tooling defect rather than a missing proof step.

A `viewable` fact names its memory too, since an object's lifetime can end
between two points. In a report about a program state, a fact from an earlier
recorded point is `at(point, viewable(p[0..n]))`, including
`at(function.entry, ...)` for entry, because `old` takes a value, not a fact.
That printed form names the historical premise. Prove it at the new point
with `have` and a frame proof. A fact of the reported state, or in a report with no
program state such as a contract check, is bare (`viewable(p[0..n])`).

A value no current local holds but a local held at a point this path
recorded reads at that point: inside a loop body, after `i = i + 1`, the
value `i` had when the iteration began is `at(region(N).entry, i)`, where
`N` is the loop's statement index, the same form a proof cites.

Rust reports use source-visible locals, slice parameters, and slice lengths
such as `bytes.len()`. Compiler-generated `__rust_` temporaries do not supply
names; a recorded point can name a copied value through its original local.

Where no source name exists, the report uses a placeholder instead of a kernel
identity: `<unnamed A>` for a value no local, parameter, read, model field or
recorded point names (a callee's result, say), and `<pointer A>` for an
address no parameter or local reaches. Placeholders share one identity within a
report and are not Click proof syntax. A fact in a refusal's proof context
that would need a placeholder is printed instead as its Surface form when that
form lowers back to the same fact in the failed proof: `*p == 0` rather than
`at(<state A>, p[0]) == 0` (`mdtests/a_refusal_names_a_fact_its_renderer_cannot_spell.md`).
A contract's own entry model prints as `old(c.model)`. Facts with no Click form, such as the
memory a step may have changed, are short descriptions
in angle brackets, in source terms: `<only p[1] changed between function entry
and here>`.

A quantifier's binder and a `match` arm's fields print under the names the
proposition was written with (`forall (b: int32) { a == b }`, `Up(u) => 1 +
d(u)`). Where that name already names another variable in the report, such as
a parameter, the binder prints as `k`, `k1`, ... instead, so the printed
proposition never captures. A binder Click introduced itself has no written
name and always prints that way.

Missing conjuncts in a direct closure and the guards of a bare instantiation in step refusals and
search-candidate details use the goal's source and recorded-point names. They are retained
as propositions and named when the report is rendered.

A `--trace-proof` run adds the checked steps on the failing path and the facts
each one added. [Reading trace output](tracing.md#reading-trace-output)
describes its notation.

## Repairing a proof from its trace

Repair a failed proof by the [proof repair procedure](tracing.md): record the goal
that failed, write the argument for it as a chain of `have` goals, and refine
the first link that does not close by identifying its primitive rule and
writing that rule's premises. Each
attempt must change that chain; a new written form, position, or tactic for the
same link is not progress. The procedure ends at a named outcome.
`missing-rule` identifies a justified inference with no supported primitive
for design discussion; it is not inferred merely from a failed search.
Use `false-claim` when a counterexample refutes the original claim. If it
refutes a requirement Click generated, check the rule that generated it.
Use `obligation-bug` when the rule or semantics do not support the
requirement. For `obligation-bug`, `inexpressible-fact`, and `tactic-bug`,
keep a reduced reproduction.
Use `unclear-output` when the available diagnostics lack the detail needed
to tell whether the proof author or Click maintainers should follow up.
Quote the output and identify what you could not determine. A diagnostic
bug report requires evidence of a specific defect in the output. When Click
prints `internal error`, use `internal-error` and preserve the original
diagnostic, command, version, and inputs.
Tooling improvements in response require discussion and user approval before
implementation, including new diagnostic content, trace presentation, or a
proof workflow. Reproduced bugs in existing behavior may be fixed
autonomously; that permission does not extend to unapproved tooling design
changes merely because they arose during debugging. If the user has already
approved the specific improvement, proceed within that scope without asking
again.

Do not conclude that repeated rejection indicates a verifier defect before
following the procedure. A clear defect such as a crash or invalid
certificate still warrants immediate investigation. Do not weaken the claim,
change otherwise-correct C, raise budgets, or add consumer-specific recovery
rules merely to get past a failure.

## Explain the program requirement first

Tactic source excerpts retain their location and show at most ten source lines,
with an explicit omission marker for longer bodies. Individual quoted lines
are limited to 160 characters; the failure reason remains outside the excerpt.

When adding or repairing a diagnostic, lead with the C operation or contract
clause being checked and `Requires` followed by the exact Click proposition or
resource clause that is not yet established. Use the user's source expressions
and retain the access mode (`owns` versus `views`), arguments, named resource
occurrence, and relevant point. An English explanation supplements this
requirement; it must not replace it.

For example, print `Requires owns counter->value` and `Available: owns
mutex_use(&counter->mutex)`. Then explain, if helpful, that `mutex_use` does not
supply the field's ownership. For a missing equality, print `Requires
counter->value == completed`. "Resource transfer failed" names neither
obligation and is not an adequate primary explanation.

Show a bounded, relevant selection of available evidence and explain the
specific mismatch. A write refused while a directly held view covers its range
names that view and explains that it permits reading only. Range-bound misses
keep their compared endpoints and the exact false or unestablished inequality.
Include the C and contract/proof locations when known;
do not invent missing locations or source origins. A refusal of a C step follows
its `C operation` line, which prints the operation as Click checked it, with
a `C statement at file:line:column` line quoting the statement as written.
The C frontend records each statement's site beside its source execution
layout, keyed by statement index, and a step names the site of the statement
it checks (`StatementSiteScope`); a site never takes part in statement
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
failure from `close()`, the implicit tail that ends every script, or another
smart search does not establish an engine bug. Split the task into smaller searches or use
simple tactics with explicit premises. When a frame proof is needed, use
`have` to establish facts at named states, `preserve` to prove unchanged
reads, and `rewrite` to carry the fact forward.

When `close()` needs to reconstruct a premise at an earlier point, its
automatic fallback probes at most 256 statement-entry points nearest the
current anchor. A premise that does not raise at the anchor therefore cannot
trigger a scan of the whole execution history. Name a relevant older point with
`at(...)`, or provide a small `using { ... }` list, when this bounded search
misses. Each candidate still has to lower to the exact retained kernel fact.
The automatic atomic fallback also declines components with more than 64
premises before rendering them; it first tries the derivation's recorded path.
This limit does not restrict an explicit `using` list. A refused written view
`close()` retains the failing construction stage, including the actual selected
premise count when it exceeds this limit, in the ordinary error and trace.
The native kernel view query and source-certificate construction are distinct:
a positive kernel query can still lack a printable checked proof. Do not infer
a missing span premise from that construction failure.

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
and at most eight premises. Individual premise renderings are truncated at 4 KiB
in an ordinary report, and reports say when additional context was omitted. In an ordinary report a
memory with no source name is labeled `<state A>`, `<state B>`, and so on, and
in a trace `state#1`, `state#2`, numbered by first appearance within one
report: equal memory shares one label and memory that differs gets another, so
"same memory" and "different memory" are visible as such. Reads of one
memory under different read names (different version points, or a version
point and the memory itself) get labels of their own, and the legend says
which label each shares its memory with and where its reads are named. The structural
comparison stops after the first 32 distinct memories. Expanded
trace facts retain further memory identities with constant-time lookup;
repeated uses of a retained version share a label. Beyond that comparison
budget, separately constructed equal memories may receive different labels.
The legend states this distinction, and the report still has fixed output and
identity-count budgets. Diagnostic labels are context, not proof
certificates. Search
context covers bounded recent representatives from loop, induction,
refinement, and common postcondition searches; it is not a complete theorem
reasoning trace. This keeps failures useful for triage without dumping
persistent proof history or repeated raw memory states.

A refused resource fold reports the instantiated body fact it could not
establish on the standard `goal:` line, and its summary quotes that fact as
the declaration writes it, after its ordinal in the declaration. If
evaluation of the fact needs an unproved prerequisite, the `goal:` line
is that specific prerequisite instead. Ordinary errors print source forms
where available. `--trace-proof` also prints the exact checked proposition with typed reads
and the report's shared memory labels. This is the rejected requirement,
not a guessed comparison with a nearby premise. Reading it alongside accepted
trace facts can reveal a difference in values or memory labels without instrumenting
the verifier.

A failing proof step names where it was written:

```text
`allocated_vector_push.contract` proof step source tactic 1 > have body tactic 2: ...
```

`source tactic 1` is the claim's source tactic occurrence, numbered exactly as
`click expand` and `click profile` address it, so the same number selects the
tactic for expansion. Each further segment descends into a block the user
wrote: `have body tactic 2` is the second tactic of that `have`'s `by { ... }`
block, and `with body tactic 2` is the second tactic of a `with` body. Inside
a block, the arms of a proof `if`, `cases`, or `all` are blocks of their own:
`else arm tactic 1` is the first tactic of the `if`'s `else` arm (`then`,
`else`, `left`, and `right` name the arms), so a tactic written after the
`if` keeps its own position in the enclosing block even though each arm
checks it. A
failure whose driver attributed no source occurrence — a planner-generated or
searched script — reports `checked step N` instead, counting the checked steps
of the block it is proving. Do not bisect a long proof with sentinel steps
before reading this location.

## Classifying smart versus simple tactics

[Smart and simple tactics](smart-and-simple-tactics.md) defines the classes:
the fallback search in `close()`, `step_until`, the implicit tail and closer, and elided
forms, which are smart while an argument is elided and simple once it is
written. Classify tactics by whether they select or plan proof operations,
not by whether the user listed every contextual input. A tactic that receives
hints and chooses among normalization, rewriting, arithmetic, transport, framing, or
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
For example: "smart `close()` failed; explicit resource transport has not yet
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

An explicit `apply(...)` inside `with(...)` reports an unavailable theorem
premise through the same checker used outside the scope. A `have f by close()`
that cannot establish its fact reports `Requires f`; neither refusal means
that resource scopes themselves are unsupported.
