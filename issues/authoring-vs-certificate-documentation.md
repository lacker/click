# Distinguish authoring syntax from expanded certificates

## Problem

Click intentionally uses one Surface Click language for handwritten proofs and
expanded certificates. That closure property is valuable, but it makes the
documentation easy to misread: smart authoring forms and exact replay forms are
often presented at equal prominence, and the larger checked-in examples contain
long exact-premise blocks without consistently explaining why they are there.

A new user can reasonably conclude that ordinary Click authoring begins by
manually listing every premise for every statement. The intended workflow is
the opposite:

1. Begin with the default prover or a comprehensible smart tactic.
2. Use `click profile` to identify a slow tactic.
3. Treat a slow simple tactic as a Click performance bug.
4. Use `click expand` on a slow smart tactic.
5. Keep the resulting simple certificate when it replays quickly.
6. Use `click audit` to check that project smart tactics remain expandable.

Total verification time may still grow with the number of fast statements and
tactics. The tools isolate and remove pathological tactic costs; they do not
promise constant verification time for arbitrarily large projects.

## Documentation structure

Reorganize the proof documentation around two views of the same language.

### Authoring view

Lead with the forms a user should normally write:

- omitted proof clauses and `by auto;`;
- smart `step()`, `execute()`, `execute_until(...)`, `summarize(...)`,
  `simp()`, `frame()`, `apply(...)`, and `transport(...)`;
- control constructs such as `have`, proof-level `if`, and `reach`; and
- simple logical/resource operations that are naturally handwritten, such as
  `intro`, `witness`, `choose`, `fold`, `unfold`, and `observe`.

### Certificate view

Then explain that exact `using` forms, `normalize`, `assumption`, explicit
derivation, and `close_invariants` are principally replay leaves. They remain
ordinary accepted Surface Click because users may inspect, edit, commit, and
debug expansion output.

Do not describe simple tactics as private or internal. The distinction is
about normal workflow and presentation, not language visibility.

## Example projects

For every certificate-heavy larger example:

- Say in the README which proof regions are concise authoring and which have
  been expanded for predictable performance or regression coverage.
- Point readers to at least one small idiomatic smart proof before asking them
  to read a long exact certificate.
- Avoid presenting generated verbosity as a recommended first draft.
- Keep the checked-in certificate when it is serving a performance or audit
  purpose; this issue does not require converting everything back to smart
  tactics.

Mdtests remain focused regression tests. They may use whichever form best
isolates the behavior under test, but prose surrounding an exact certificate
should say when exact replay is the subject.

## Style guidance

Add a short, explicit style policy:

- Prefer the highest-level tactic that is fast, predictable, and easy to
  understand.
- Expand based on profiler evidence, not preemptively.
- Prefer a checked simple certificate over a pathologically slow smart tactic.
- Do not hide a slow simple leaf by wrapping it in automation; report and fix
  it as a Click bug.
- Use stable region labels in maintained proofs instead of numeric statement
  IDs when practical.
- Prefer the canonical compact proof spelling documented by the language.

## Dependencies

Implement this after
[exact-premise-syntax-cleanup.md](exact-premise-syntax-cleanup.md) and
[canonical-proof-spelling-and-printing.md](canonical-proof-spelling-and-printing.md),
or update it again when those issues land. The documentation must describe the
accepted and printed syntax, not a proposed intermediate state.

Binder unification is independent and should not block this issue.

## Acceptance criteria

- The basic proof documentation teaches the authoring workflow before exact
  certificate syntax.
- `docs/proof-tactics.md` remains exhaustive, but visibly distinguishes common
  authoring forms from exact replay forms.
- Performance-tool documentation states both the pathological-tactic goal and
  the unavoidable aggregate cost of many fast tactics/statements.
- Certificate-heavy example READMEs identify why exact blocks are checked in
  and direct learners to a concise starting proof.
- Documentation consistently explains that expanded certificates are ordinary
  maintained Surface Click, not a private dialect.
- All snippets use the canonical syntax present when the issue lands.
- Mdtests for documentation snippets pass.
