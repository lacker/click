# Audit recursive resource/call composition

## Dependency and outcome

Perform this audit after the recursive zero-list example exists. It is a
bounded review-and-cleanup chunk, not a presumption that the resource logic must
change. If the audit finds no defect, close it with tests or documentation that
make the successful boundary explicit.

## Why an audit is separate

Focused mdtests establish individual rules. A recursive traversal makes those
rules interact across several state boundaries:

- an entry composite resource is conditionally opened;
- a field load names the recursive child;
- an opaque self-call receives that child resource;
- its result is stored in a C local;
- its returned view or ownership must fit the parent proof; and
- branch-local facts must survive only through explicit, certified interfaces.

A workaround in the example could hide a general source-level wart. Conversely,
turning every awkward proof line into new language machinery would overreact.
Review the complete flow once, classify findings, and keep the cleanup small.

## Audit checklist

### Resource boundary

- `observe` on a viewed recursive resource exposes one layer of pure facts and
  viewed children, never write authority.
- `unfold` on owned resources consumes exactly the parent and exposes exactly
  one body layer; `fold` requires that layer back.
- Null guards decide the empty body without reading memory before permission is
  available.
- Equality between a loaded tail and a C local lets the exact declared child
  resource satisfy the recursive callee, without globally expanding unrelated
  recursive branches.
- A recursive call cannot duplicate owned parent and child resources or retain
  both after consuming one lineage.

### Opaque-call boundary

- The recursive call uses the provisional exact contract rule for its closed
  call-graph transaction; it never falls back to body execution.
- Requirements, public postconditions, returned resources, and mutation
  summaries are all instantiated at the call's exact arguments and entry
  snapshot.
- Public results can be named through C locals and program points.
- Havoc identities, provisional-rule handles, and resource implementation
  details remain unavailable to Surface Click proofs.

### Proof tooling and diagnostics

- `click profile` attributes cost to the actual tactic; no simple replay step
  becomes slow because terms contain recursive resource snapshots.
- `click expand` produces a replayable, source-spellable certificate for every
  slow successful smart step in the example.
- A missing unfold/observe, wrong child argument, absent result fact, or
  unreturned resource produces a local diagnostic rather than a late generic
  contract-certification failure.
- Documentation examples use the tactic names and behavior the verifier
  actually accepts.

## Classification rule

Fix findings here only when the correction preserves the established model:

- source spelling and program-point selection;
- exact public fact transport;
- deterministic one-layer fold, unfold, or observe behavior;
- resource equality using already-proved argument equality;
- focused diagnostics; or
- an obvious performance bug in a simple tactic.

Create or update a separate issue before changing any of these:

- the meaning of owned or viewed resources;
- the guarded-recursion acceptance rule;
- recursive call-graph certification;
- termination evidence;
- automatic recursive unfolding; or
- theorem induction.

Do not add special cases named after `zero_list`, a particular C field, or the
example directory.

## Regression expectations

For each fixed wart, add the smallest mdtest or unit test that fails without
the fix. Keep the larger example as integration coverage rather than the sole
regression. Include negative tests for any authority or information-hiding
boundary touched by the change.

## Acceptance criteria

- Every checklist item has been inspected against the example and relevant
  focused tests.
- Any fix is generic, small-to-medium, and independently tested.
- The example verifies without quarantine and within tactic budgets.
- Expansion never emits kernel-private identities.
- No finding is silently deferred: it is fixed, documented as intentional, or
  written as its own issue with a reproducer.
- This audit document is deleted when that classification is complete.
