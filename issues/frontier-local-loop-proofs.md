# Make loop proofs local to the execution frontier

## Problem

Click currently separates a loop proof into two distant operations:

```click
for loop(0) {
    invariant 0 <= i;
    invariant i <= n;
    initialize by simp;
    preserve by {
        step();
        close_invariants();
    }
}

ensures result == n by {
    summarize(loop(0));
    ...
}
```

The structural clause is verified by a separate traversal from function entry.
The ordinary contract proof later consumes its globally registered rule.  That
model duplicates traversal, makes the proof context at the declaration hard to
understand, and asks users to identify a loop by a source-order number even
though execution already has a precise current position.

An execution proof owns an **execution frontier**: the boundary between C that
has been verified and C that remains.  A loop proof should operate on the loop
at that frontier, just as structured branch reasoning operates on the current
control flow.  It must not search for, jump to, or reconstruct the entry of a
separately named loop.

## Language design

Add a frontier-local structural tactic:

```click
by {
    step();
    loop as fill {
        invariant 0 <= i;
        invariant i <= n;
        mutable p[0..n] by frame;

        initialize by {
            simp();
        }

        preserve by {
            step();
            close_invariants();
        }
    }
    have at(fill.exit, i) == n by simp;
    step();
}
```

`as fill` is optional.  When present, it names the loop's entry and exit
snapshots; it does not select a source region.

The operator has these semantics:

1. The current execution frontier must be at a C loop.  Otherwise it fails
   promptly with a diagnostic naming the current statement.
2. `initialize` is a pure proof at the actual entry frontier.  It establishes
   the declared invariant bundle there.
3. `preserve` is an execution proof beginning at a fresh arbitrary-iteration
   frontier with the invariant and true guard.  Every path must reach the back
   edge with the invariant and effects reestablished.
4. Successful phases construct the existing kernel-checked loop rule, apply
   it once, and advance the enclosing frontier to the loop exit.
5. The arbitrary-iteration context is scoped and cannot leak into the
   enclosing proof.  The exit receives only the checked invariant, false
   guard, effects, resources, and snapshots exported by the loop rule.
6. `decreases` remains optional.  Its absence means partial correctness and
   must not manufacture a return frontier for a perpetual loop.

The block is a control-flow tactic, not smart search.  Its nested proofs retain
their own smart/simple classifications.  `click profile` attributes work to
those nested tactics, and `click expand` recursively replaces their smart
steps with replayable simple certificates.

Tool selection remains source-based.  An explicit smart tactic is selected by
its ordinary one-based `PATH:LINE:COLUMN` location.  The profile may describe
that location with a breadcrumb such as `loop fill / preserve / step`, but no
`preserve tactic 0` spelling becomes part of Surface Click.  The internal AST
path exists only to map timing and expansion back to the source character.

Omitted phases remain convenient automation; users must not write `by auto`
merely to create a tooling anchor.  The `loop` keyword is the shared source
location for all omitted initialization and preservation automation in that
block.  Expanding it materializes every omitted phase at once.  If a phase is
explicit, its keyword and the tactics in its proof provide their own source
locations and can be expanded independently.  Audit deduplicates the shared
loop-keyword location.

## Implementation boundary

There must be one loop-proof engine during migration.  Extract an operation
that accepts the actual entry state and loop description, verifies
initialization and preservation, constructs a `CVerifiedLoopRule`, applies the
rule, and returns the exit frontier.  The legacy structural traversal may call
that operation temporarily; do not create a second verifier for the new
syntax.

Today structural loop clauses are lowered into the annotated kernel C function
before a contract proof starts.  A frontier-local block does not acquire a loop
identity until replay reaches it.  Extract loop-annotation lowering so the
surface block can be lowered for the loop actually at the frontier.  Do not
preassign an implicit `loop(N)` by approximating proof-script movement: that
would recreate the detached traversal and would be wrong across proof
branches.

## Migration

Land the change in independently green stages:

1. Extract shared loop lowering and rule construction without changing syntax.
2. Add the frontier-local parser, replay operation, diagnostics, and focused
   kernel-boundary tests while retaining the old syntax.
3. Add recursive expansion, profile, audit, and printing support for the
   structural block.
4. Migrate loop mdtests, then small scalar examples, `perpetual-service`,
   resource-mutating examples, nested/branch-local loops, and finally
   `owned-vector`.
5. Make ordinary `step()` and `execute()` stop locally at an unhandled loop.
6. Remove `summarize(loop(N))`, function-level `for loop(N)` clauses, their
   preliminary traversal, and obsolete global rule registration.

Grouped function proofs should be preferred when several claims share one
execution.  Per-claim execution proofs may also use `loop`; each proof is
independent and may validly establish a different sufficient invariant.

Removing `for statement(N)` is a separate change.  Statement assertions,
static labels, and snapshots need their own frontier-local replacements and
must not be swept into the loop migration merely because they share the old
`for` parser.

## Regressions

Focused tests must cover:

- one scalar `while` loop and one lowered C `for` loop;
- entry after explicit straight-line and resource tactics;
- a loop reached inside one branch;
- nested loops;
- whole-loop and step-relative mutable effects;
- labeled entry and exit snapshots;
- optional `decreases`;
- a perpetual loop with no return frontier;
- a prompt error when the frontier is not at a loop; and
- full profile/expand/audit replay of smart nested phase proofs.

In particular, a regression must prove that facts and resources established by
earlier tactics in the enclosing execution proof are available to
initialization.  No implicit function-prefix traversal may be used to recreate
that context.

## Acceptance criteria

- `loop { ... }` verifies exactly the loop at the current execution frontier
  and advances the enclosing frontier to its checked exit.
- The new path reuses the existing kernel loop rule and a shared proof engine.
- Labels name the encountered loop but never select or seek to one.
- Nested smart tactics expand and freshly replay through all three tools.
- Wrong-frontier and missing-loop-proof failures are prompt and concise.
- Repository loop proofs migrate without C changes or raised tactic budgets.
- The legacy syntax, detached traversal, and `summarize` tactic are removed
  only after all checked users have migrated.
