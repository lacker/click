# Bound smart framing and expansion end to end

## Problem

The owned-vector investigation exposed a smart `frame()` that crossed its
normal two-second tactic budget. With a larger expansion budget, `click expand`
continued beyond a minute without producing an artifact and required manual
interruption. A shorter bounded run also surfaced an ordinary resource
validation error instead of clearly reporting the expired deadline.

The exact `frame using` replay for the same kind of effect is cheap. Smart
framing should select the small dependency boundary needed by that exact
certificate. It must not build a contextual reasoning database from every
ambient memory snapshot or postpone its only deadline check until an expensive
inner operation returns.

## Intended regressions

Add a small C function with one write and one matching mutable segment. Its
proof should accumulate many irrelevant snapshot and pure facts before a smart
`frame()`.

Test all of the following:

1. `frame()` completes within its default smart budget.
2. `click expand` emits a small `frame using` certificate.
3. The emitted artifact verifies directly and passes the corresponding audit.
4. Adding irrelevant facts does not materially change exact-frame cost or the
   selected certificate premises.
5. A deliberately exhausted CLI deadline fails near its configured bound,
   names the interrupted phase and tactic, writes no artifact, and leaves no
   verifier process running.
6. Deadline exhaustion cannot be converted into an ordinary proof,
   validation, or missing-resource diagnostic.

Use an internal deterministic deadline test in addition to the CLI regression
so the suite does not depend solely on wall-clock scheduling.

## Design constraints

- Separate exact certificate replay from contextual smart search. Exact replay
  must inspect only its named premises.
- Make every potentially large frame-planning and certificate-construction
  loop cooperatively check the active deadline.
- Preserve the timeout as a distinct error while it propagates through
  resource validation, proof planning, expansion, and the CLI.
- `--time-limit` must bound the complete requested operation, including source
  discovery, certificate generation, self-verification, and output handling.
- Do not solve the problem by retaining a hand-copied enormous certificate,
  raising the time limit, using a wrapper process, or simplifying the C.

## Acceptance criteria

- Smart framing produces and replays a minimal exact certificate within its
  normal budget.
- Successful expansion always self-verifies before writing output.
- Exhausted expansion fails promptly and explicitly without partial output or
  stale processes.
- Profile, expand, audit, and direct verification agree on the selected site
  and its outcome.
- The default test suite passes with the regression's irrelevant context left
  intact.
