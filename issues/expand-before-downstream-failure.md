# Let expansion diagnose an earlier hotspot when a later proof fails

## Problem

The owned-vector profile reports a successful four-second
`execute_until(statement(4))` and instructs the user to expand it. `click
expand` finds the rewrite, but refuses to write the output because a later,
independent `step() using` in the same proof is already stale. The user cannot
inspect or replay the expansion that the profiler prescribed, so the normal
profile-then-expand debugging loop deadlocks behind an unrelated downstream
failure.

Expansion must not claim that a whole proof is green when it is not. At the
same time, discarding a successfully reconstructed local certificate makes it
unnecessarily difficult to repair proofs from the first failing or slow site
forward.

## Violated invariant

`click profile` and `click expand` should form a usable debugging workflow even
while a proof is under repair. A profiler recommendation must have a bounded,
honest way to expose the corresponding local certificate.

## Intended regression

Create a small proof with two sequential tactics:

1. an earlier successful smart tactic with an expandable certificate; and
2. a later intentionally invalid explicit certificate.

Target expansion at the first tactic. The result must make the earlier
certificate available without describing the entire proof as verified, and
must clearly preserve the later failure.

## Design question

Choose an explicit contract for partial output. One plausible interface is a
diagnostic-only mode that prints or writes a candidate marked **unverified past
the targeted tactic**, while the existing `--in-place` mode remains atomic and
requires full targeted-proof verification. Another is prefix verification plus
a structured patch artifact that cannot be mistaken for a verified sidecar.

Do not silently weaken the existing verification guarantee for ordinary
`click expand --output`, and do not require users to scrape stderr or invoke an
internal wrapper.

## Acceptance criteria

- The regression exposes the earlier expansion despite the later proof error.
- Output clearly distinguishes prefix-checked or candidate output from a
  fully verified expanded proof.
- `--in-place` remains atomic and never installs an unverified proof.
- The command stays within the normal project and tactic budgets.
- The profile guidance names the appropriate mode when full expansion is
  blocked by a downstream failure.
- CLI documentation and expansion tests describe the guarantee precisely.
