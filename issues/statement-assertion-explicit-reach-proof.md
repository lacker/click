# Let statement assertions prove how they reach their program point

## Problem

`for statement(N) { assert ... }` verifies its own implicit symbolic traversal
from function entry to `statement(N).entry` before it checks the ordinary
function proof. That traversal is independent of the function proof script and
currently has no Surface Click proof of its own.

The source-faithful owned-vector prototype exposes the consequence. After the
unchanged general `vector_push` call, the ordinary function proof explicitly
repackages `vector_storage(owner)` as `nonempty_vector(owner)` and supplies
`0 < owner->len` to the following `vector_get` call. A later
`for statement(6)` assertion nevertheless fails while its separate implicit
traversal crosses `statement(4)`:

```text
execution proof traversal at statement(4) is missing prerequisite
(vector_get precondition): condition-certificate premise search did not derive
signed less-than is true ...
```

Replacing the ordinary proof's broad `execute_until` with
`step() using { 0 < owner->len; }` does not affect this failure. The implicit
traversal cannot see that explicit premise or the resource unfold/fold steps.
Once the pure prerequisite is supplied, the same boundary must also be able to
replay the resource repackaging required by `views nonempty_vector(owner)`.

This violates the smart-search escape-path rule. Search may fail, but a user
must be able to continue with explicit simple tactics. Today a statement
assertion can explicitly prove the proposition *at* its point, but cannot prove
the execution/resource path used to reach that point.

## Why this blocks the vector work

Deleting the assertion, moving it into the ordinary function proof, retuning
condition search, or changing the C would all avoid the failing path without
fixing statement assertions. The assertion is a valid independent claim and
must remain the regression. The vector prototype is preserved in the detached
`/private/tmp/click-expansion-probe` worktree while this issue is open; `master`
remains at the green source-fidelity checkpoint.

## Direction after the frontier-model review

Do not add a second execution script inside the structural clause.  An earlier
proposal suggested:

```click
for statement(6) as read_replacement {
    reach by {
        execute_until(statement(4));
        unfold(vector_storage(owner));
        fold(nonempty_vector(owner));
        step() using { 0 < owner->len; }
        execute_until(statement(6));
    }

    assert owner->len == 1 by auto;
}
```

That would make an out-of-band assertion marginally more controllable while
preserving the underlying problem: a static declaration would still own a
separate execution from function entry.  It would also introduce another way
to move through C alongside the ordinary frontier-based proof.

The preferred direction is to express statement-local obligations in the
ordinary forward execution proof, at the frontier where the statement is
actually encountered.  Branches and loops should open scoped structural
subproofs from that same frontier.  The loop half of this cleanup is tracked in
[`frontier-local-loop-proofs.md`](frontier-local-loop-proofs.md).

The statement replacement still needs a focused design.  It must account for:

- asserting a proposition at the current frontier without re-executing a
  function prefix;
- naming static statement entry/exit snapshots without turning the name into a
  jump target;
- preserving independent contract claims and grouped proofs; and
- removing `for statement(N)` only after every remaining use has an ordinary
  forward-proof spelling.

Until that design lands, retain the source-faithful failing assertion as the
regression.  Do not add `reach by`, tune automatic traversal, relocate the
assertion, change the C, or delete the check merely to unblock the vector
example.

## Intended regression

Add a small multi-function mdtest with two representations of the same backing
resource:

1. a first modular call changes a scalar and returns the general storage
   resource;
2. reaching a later modular call requires an explicit pure bound and folding
   that storage as a stronger view resource; and
3. a statement assertion after that call proves a simple fact.

The automatic structural traversal should reproduce the current failure.  The
eventual frontier-local statement form should verify in the ordinary proof
after its explicit resource and execution steps.  Keep the relevant
bound/resource conversion out of the first facts in the context so the
regression does not accidentally depend on condition-fact ordering.

## Acceptance criteria

- Statement assertions have a documented Surface Click spelling at the current
  execution frontier; they do not own a separate function-prefix traversal.
- Ordinary `step() using`, `unfold`, and `fold` steps can establish their exact
  context before the assertion is checked.
- Smart steps in the enclosing proof are profiled, expandable, freshly
  replayed, and audited.
- Static labels name program points and snapshots but do not seek to them.
- The focused mdtest and the unchanged owned-vector pipeline assertion pass
  without changing C or deleting/relocating the assertion.
- The default suite, profile, expansion, and audit gates remain green.
