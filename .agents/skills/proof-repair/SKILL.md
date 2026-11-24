---
name: proof-repair
description: Repair a failed Click proof from its goal and trace. Use whenever `click verify` refuses a proof, or an omitted proof, `close()`, `step()`, or `step_until(...)` does not prove what you expected, before changing the proof, the contract, the C, or the verifier.
---

# Repairing a failed proof

Follow the proof repair procedure until it reaches one of the outcomes
below. `click docs tracing` shows the procedure and explains how to read a
trace. `click docs NAME` prints a tactic's forms, class, and documented
behavior.

## Crashes and hangs

Two failures are bugs whatever the proof says, and end this loop at once:

- `crash`: Click exits without a report: a panic, an abort, a stack
  overflow, or the process being killed.
- `hang`: Click runs for minutes without returning a report. Stop it and
  note how long it ran. A wall-clock timeout can also result from CPU
  starvation, so check whether the run was making progress.

Do not change the proof, raise a limit, or retry to get past either one.
Report it (below), labelled `crash` or `hang`, with the exact command, the
`click --version` output, the complete output, and the files needed to rerun
it; shrink them if you can, but a report need not wait for that.

## 1. Classify the error

- `syntax error` or `type error`: fix the reported source. This skill does not
  apply.
- `unsupported`: identify the documented limitation and quote the refusal. If
  a supported route preserves the original claim and target program, try it.
  Otherwise stop at `unsupported` and explain how the user can request support.
- `internal error`: stop at `internal-error`. Click has reported its own
  failure. Capture the error, version, command, and inputs.
- `work limit reached`: stop at `work-limit-reached`.
- `timed out`: stop at `timed-out`. If the run was hung, follow the `hang`
  workflow above.
- `tactic error`: read `click docs TACTIC` and check whether the tactic is valid
  at the reported point. Correct an invalid invocation. If the invocation and
  its premises satisfy the documented rule and Click still refuses, report
  `tactic-bug`. For a written or implicit step that names required evidence,
  check whether the operation is viable at that program point. An operation
  that reads an uninitialized value may require a change to the program or
  contract. A `goal:` line identifies an issued proof obligation.
- `contract error`: identify the written clause and read the documented
  contract rule that Click says it violates. Check the rule under the
  contract's stated requirements. If the clause violates it, explain why to
  the proof author and check the intended correction. If the original contract
  satisfies the rule and Click still rejects it, stop at `contract-bug`.
- `unsuccessful search`: explicit or implicit proof search ran and found no
  proof. This includes search that exhausted its own work budget. Record the goal. If it holds, write an explicit chain of smaller
  links, or supply the missing argument or premises.
- `incomplete proof`: the proof ended with a requirement still outstanding.
  Record what the report says the proof must establish and the path where it
  is required. Add the missing steps before the proof closes. For missing
  termination evidence, follow the reported call chain to the unranked loop
  or recursive call and prove the missing descent there. For a return
  resource, account for the units held on that path and what must go back to
  the caller. Use each owned unit once. If the resource can be assembled from
  parts already held, write the corresponding fold. If an allowed execution
  cannot supply what the contract promises, follow the `false-claim` procedure.
  If Click demands something the closing rule does not require, follow the
  `obligation-bug` procedure.

Use `unclear-output` when the available diagnostics lack the detail
needed to tell whether the proof author or Click maintainers should follow
up. Check the ordinary diagnostic, the applicable documentation, and the
trace when available. A contract error may omit the clause or rule you
need to check, or an implicit-step refusal may omit the operation Click tried.

## 2. Record the goal

From the ordinary report, write down:

- the goal `G`, from the `goal:` line or the named requirement in an
  `incomplete proof` report;
- the program point where `G` is required (a C statement requirement is a goal
  at that statement's pre-state);
- the premises available there.

If the report does not explain the premises, rerun the command under
`To get a trace:` (`click verify --trace-proof PROOF SIDECAR`, optionally with
`--trace-to LINE`). Read its `proof refusal` section.

A goal about memory (any `transport`, frame, or `read<...>(state#N, ...)`
goal) depends on its `state#N` and `value#N` labels: write down the legend
line that defines each label the goal uses. Two written forms of one C address
(`p` and `g + 16 bytes`, or a read at entry and a read in the loop) are often
the whole story. Otherwise ignore the legend.

A named resource and return path can identify a requirement directly.
Use `unclear-output` when the available output leaves the requirement or
its program point unclear.

## 3. Decide whether `G` is true

Check `G` against the contract, the branch facts, and the C semantics. On an
execution that refutes `G`, also check the original claim and the rule that
introduced `G`.

- If the execution refutes the original claim, stop at `false-claim`.
- If Click introduced `G` and the applicable semantics or documented rule
  do not require it, stop at `obligation-bug`. Show what the rule requires
  at this point and why the original claim can hold on this execution.
- If the proof author chose a stronger intermediate goal than the argument
  needs, revise that step and continue.

## 4. Write the argument as a chain

For a proposition, write why `G` follows from the premises as intermediate
facts, each one a `have` at the program point:

```text
have A by { ... }
have B by { ... }
// G now follows from A and B
```

The original proof or overall argument may give a reason to expect success.
Check that the local goal follows at this program point. If you cannot justify
that step or give a counterexample, stop at `unclear-goal`. If you can justify
it but cannot write a needed intermediate fact in Click, use
`inexpressible-fact`.

## 5. Run, then refine the first failing link

The first link that fails becomes the new `G`; go back to step 2.

For one recorded transition, write
`preserve(B, region);` under a read-equality goal.
The execution-produced footprint includes stores, call effects and releases;
no free-specific rule is needed. Establish footprint separation with explicitly
selected premises in `normalize() using`. Compose transitions with
`have`, `rewrite`, and `close()`. Spell out each transition in the proof. Read the limits in
`docs/reference/tactics/index.md#preservation`; unsupported resource
effects are not grounds for silently falling back to a history search.

Before refining, use the primitive-rule map in
`docs/concepts/tracing.md#identify-the-primitive-rule` and the full **Accepts**
list of the referenced tactic. State the rule, its instantiated premises, and
its conclusion. The library reference supplies named mathematical laws;
the tactic reference supplies logical, execution, resource, and transport rules.
Count logical rule applications, not tactic calls: a single tactic can hide a
walk, while an explicit certificate can contain several primitive steps.

A refusal lists `refused by:` when Click can identify the tactic.
An `incomplete proof` names the requirement to establish before closing.
A failed `close()` leaves the question of which primitive rules apply open. Split a link that
needs several rules into links justified by those rules. Stop when all the
premises of a documented primitive are written. If a concrete, justified
inference has expressible premises and conclusion but no supported primitive,
stop at `missing-rule` for design discussion; do not keep asking for smaller
facts without a rule that could connect them.

For memory preservation, one checked store transition, the read's value at
its pre-state, and separation of the full read from its writes must support a
fast primitive. Work may scale with those explicit inputs and effect, not
with earlier history. Internal cache/forget/read-origin constructions are not
extra program steps the author should have to prove. This is a design
requirement, not a claim that all current transport paths implement it.
Transport that searches across several transitions must expand to explicit
primitive applications with their transitions and premises; replay must not
rediscover the history. A `using` list alone does not guarantee fast checking.
For a successful proof that still walks history, follow verifier-design and
retain a deterministic scaling reproduction instead of calling the cost fixed.

To split a link a smart tactic proved part of, read its trace. A step marked
``(from `implicit tail`)``, ``(from `step_until`)``, ``(from `close`)`` or
``(from `implicit closer`)`` is one that smart work took (the implicit tail's
execution or its closer, a written `step_until`, a written `close()`, or the
closer of a step's requirement), and a `chosen:` line is the written form of an argument its
search chose. Writing those steps and forms out turns the searched part of
the link into simple tactics, so the remaining gap is the link to split.

A refusal that says "this is a search miss" came from an elided form, such
as `apply(t(x))` or a bare `transport(P, Q)`, whose search for an argument
found nothing. Write the argument: state the missing fact with `have` first,
or write the `using` form it names. Only the written form's refusal can be
`tactic-bug`.

Before each run, state in one line which link is new and why it holds. A new
tactic, written form, or position for the same link is not a new attempt. Never
edit proof search or the implicit closer, raise a budget, or change the C to get
past a link.

## 6. Shrink a refused simple link

Before reporting a refused simple link, make the link itself as small as it
will go, not only the program around it:

- Drop each `using` premise, alias, and earlier `have` it does not need, one
  at a time, keeping the refusal.
- Write it with the most direct form: the C local the statement uses
  rather than a spec alias for it.
- Find the nearest link that passes, such as the same transport of another
  field across the same store, and say what differs between the two (the
  field's type and width, its offset, how the address is written).

Then compare the refusal with the one-line argument and name the step Click
did not take: which two addresses it did not identify, which read it did not
carry, which fact it did not read.

## Outcomes

State the status in every user-facing proof-repair update. When the repair
fails, name exactly one failure category in the report that announces the
failure. Use the categories below or `crash` or `hang` as defined above. When
diagnosis or repair is still underway, say it is in progress and name the
current proof step or question. Use `success` once the proof verifies.

Stop at exactly one outcome:

- `success`: the proof verifies. Keep the explicit links the default
  automation needed.
- `false-claim`: an execution admitted by the contract violates the original
  claim. Give the counterexample. The proof author follows up on the claim,
  contract, or program.
- `obligation-bug`: Click generated a requirement unsupported by the
  applicable semantics or documented rule. Show the required goal, its
  program point, and the obligation the rule actually calls for. Click
  maintainers follow up on obligation generation.
- `unclear-goal`: you can read `G` and its premises, but the investigation
  produced neither a mathematical argument for `G` nor a counterexample.
  Say why you expected the proof to work and identify the exact step where
  that expectation lacks a justification.
- `missing-rule`: the premises and conclusion are expressible and the
  inference is justified, but no supported primitive connects them. Preserve
  the rule schema, references checked, and reduced example for design
  discussion. A search miss alone does not establish this outcome.
- `inexpressible-fact`: the argument needs an intermediate fact that Click
  cannot write. Follow the user-facing reporting instructions below.
- `contract-bug`: Click refuses a contract that satisfies the applicable
  documented contract rule. Quote the exact clause and refusal, cite the rule,
  and show how the written requirements and resources satisfy it. Click
  maintainers follow up on contract checking.
- `tactic-bug`: a bug in Click. The minimized link is one simple tactic,
  its written premises justify the goal, and the tactic's documented
  **Accepts** list in `click docs NAME` covers the link. Click still refuses
  it. Report the exact refusal and the applicable documentation.
- `unclear-output`: the available diagnostics leave responsibility
  undetermined. Quote the output verbatim and name the missing or
  ambiguous detail. Say what it prevented you from checking.
- `unsupported`: a documented capability limit prevents the original case
  from being checked. Name the exact limitation and cite its documentation.
  Describe any supported route and the documented path to supporting the
  original case. The proof author can choose the supported route or request
  support from Click maintainers.
- `work-limit-reached`: Click reached the overall `--work-limit`. Give the
  work limit and the operation where checking stopped. Profile the run if
  the work is unexpected.
- `timed-out`: wall-clock containment stopped Click before a verdict. Give
  the time limit and the last reported operation, if available.
- `internal-error`: Click itself reports `internal error`. Tell the user
  immediately that Click detected a verifier failure. Use the original
  diagnostic. A proof goal and a minimized tactic link are optional evidence.

The trace’s `proof refusal:` section shows where the CLI outcome arose.
To report a `tactic-bug`, show why the inference holds and cite the documented
behavior the refusal violates. A smart-tactic miss or a search for an omitted
argument calls for an explicit proof link. While checking the rule or its
premises, report that diagnosis is in progress. Use `unclear-goal` if you
cannot justify the goal after investigation.

In the outcome report, say explicitly what the result establishes about
Click. `contract-bug`, `obligation-bug`, `tactic-bug`, `inexpressible-fact`,
`internal-error`, `crash`, and `hang` identify Click defects. File a
diagnostic bug from `unclear-output` only when you can demonstrate a
specific defect in the output. `false-claim` gives a counterexample to
the original claim.
`unclear-goal` leaves the truth of the goal open. `missing-rule` identifies a
gap in supported inference.

## Reporting an inexpressible fact to the user

In the update that reports the outcome, explicitly call it an
`inexpressible-fact` failure. State the exact intermediate proposition in
the verifier's notation or in precise mathematical terms. Identify the part
that has no Click source form, such as a consumed resource model, a program
point, or a range with a specific bounds identity. State which larger goal
the intermediate fact would help prove.

Quote the relevant verifier output verbatim, including the `goal:` line or
the `no Surface form` diagnostic when present. If the output only names the
larger failed goal, quote it and explain how the trace identifies the
inexpressible intermediate fact. Give this summary when reporting the
failure to the user, before asking for approval to file a bug.

## Requesting support

If the user wants to request support, prepare a reduced example, the exact
command and CLI output, and the capability the example needs. Cite the
documented limitation and explain what the supported alternatives would
require changing. Get approval before opening a feature request in
[Click’s issue tracker](https://github.com/clicklang/click/issues).

## Reporting a bug

Report a Click defect as follows:

1. Get the user's approval before reporting it.
2. Open an issue at https://github.com/clicklang/click/issues.
3. Give the report below, enough for someone else to reproduce it.
4. Label the issue with its outcome: `tracing: inexpressible-fact`,
   `tracing: contract-bug`, `tracing: obligation-bug`, `tracing: tactic-bug`,
   `tracing: unclear-output`, `tracing: internal-error`, `crash`, or `hang`.
   Start the title with it in brackets too (`[tactic-bug] ...`,
   `[hang] ...`), so it shows even where you cannot set labels.

## What a bug report contains

For `internal-error`, give the exact command, `click --version`, the complete
error output, and the inputs needed to reproduce it. Quote the message that
identifies the verifier failure. For crashes and hangs, follow the requirements
above.

For `contract-bug`, give a reduced contract and enough of the target program
to reproduce the refusal, the exact command, `click --version`, and the
complete output. Cite the documented contract rule and show how the
original clause satisfies it under its stated requirements. An entry
diagnostic may have no `goal:` line or written tactic. Report the exact
clause and refusal in that case.

For `obligation-bug`, give a reduced reproduction, the original claim, the
generated goal at its program point, and the exact command and output.
Cite the rule or semantics that governs the check. Show the discrepancy,
including any execution that satisfies the original claim while refuting the
generated goal.

For a confirmed diagnostic defect found during `unclear-output` triage,
give the reduced inputs, exact command, `click --version`, and complete
output. Identify the missing or misleading detail, show the evidence for
the discrepancy, and say what the output should have made clear. Include
a trace, goal, or proof link when it helps demonstrate the defect.

For `tactic-bug` or `inexpressible-fact`, give:

- The smallest C and Click that still fail, with the original source pattern,
  and the exact command and its output, including the `goal:` line.
- The chain up to the failure, with every earlier link proved.
- The failing link in its smallest form (step 6): its goal, the tactic, and
  the refusal, with the legend lines for every label the goal uses.
- The nearest passing link and what differs from it.
- Why the link holds, in one line of mathematics, and the step of that
  argument Click did not take.
- For `tactic-bug`, the item of that tactic's **Accepts** list that
  covers the link.
