# Make `intro` bind a variable fresh with respect to the available facts

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0) and `click audit` (passes) on a false postcondition
about a terminating C function.

Every surface proposition lowerer restarts binder numbering at 2_000_000 per
separately lowered proposition: `KernelPropositionLowerer::new`
(`src/surface/lowering/proposition_lowering.rs:30`, allocation at `:120` and
`:145`) on the pure path, and `lower_fixed_state_proposition_with_assumptions`
(`src/surface/proof/fixed_state_proofs/have_proofs.rs:37`, restart at `:107`)
on the fixed-state and execution path the regression exercises.
`Proof::begin_have`
(`src/surface/proof/proof_object/splits_and_scopes.rs:842-905`) lowers the
`have` goal with a fresh lowerer through `lower_surface_goal`
(`src/surface/proof/surface_lowering.rs:197`) while inheriting the enclosing
branch's facts (`splits_and_scopes.rs:899`), which after an earlier `intro`
already mention `Variable(2_000_000)`. Kernel `apply_intro`
(`src/kernel/proof/object.rs:605-621`) turns `ForAll { var, body }` into the
goal `body` with `var` itself free, without renaming; the surface wrapper
(`src/surface/proof/proof_object/step_application.rs:1157`) only records the
binding name. The kernel therefore relies entirely on surface freshness, and
the surface does not provide it.

Escalation: the captured `have` publishes a false universal, which discharges
a false loop invariant; the surface marks initialize and preserve proven
(`src/surface/proof/execution_planning/forward_planning.rs:776-801`), the
kernel loop rule then emits no invariant obligations
(`src/kernel/loops.rs:495`), the exit fact propagates, and contract
certification proves the false ensures.

## Violated invariant

A universally quantified goal introduced by `intro` must bind a variable that
does not occur free in any available fact. The kernel operation that performs
the introduction must guarantee that itself; it must not depend on how the
surface numbered the binder.

## Intended regression

```c
int32 bad(int32 x) { while (x < 1) { x = x + 1; } return x; }
```

```click
verifying "bad.c";
int32 bad(int32 x) { requires x == 0; ensures result == 5; } by {
    loop { invariant x == 5;
        initialize by {
            have forall (u: int32) { u == 5 implies forall (z: int32) { z == 5 } } by {
                intro(); intro();
                have forall (w: int32) { w == 5 } by { intro(); assumption(); }
                assumption();
            }
            have x == 5 by {
                instantiate(forall (u: int32) { u == 5 implies forall (z: int32) { z == 5 } }, 5) using { }
                instantiate(forall (z: int32) { z == 5 }, x) using { }
                assumption();
            }
            assumption();
        }
        preserve by { step(); /* same two have blocks and assumption() */ }
    }
    step(); simp();
}
```

`bad(0)` returns 1. Today verification exits 0 and audit passes. After the fix
the inner `have forall (w: int32) { w == 5 }` must fail with a diagnostic
naming the unclosed goal. The discriminating control (wrap the outer goal in
one more `forall (a: int32)` and add a third `intro()`) already fails and must
keep failing.

## Acceptance criteria

- `apply_intro` in `src/kernel/proof/object.rs` renames the binder to a
  variable fresh with respect to the branch's facts, resources, and execution
  state before exposing the body, or rejects the introduction when the binder
  occurs free; the same guarantee covers the legacy `Intro` in
  `src/surface/proof.rs:168` if it survives.
- A kernel unit test introduces `forall v. P(v)` in a context whose facts
  mention `v` free and asserts the exposed goal does not mention the fact's
  variable.
- The regression above fails; a positive mdtest with the same nested `have`
  shape and consistent binders verifies.
- `scripts/check.sh` passes.

Related: [kernel-binder-hygiene.md](kernel-binder-hygiene.md) tracks the
numbering convention this bug exploits;
[legacy-pure-theorem-checker.md](legacy-pure-theorem-checker.md) is the same
mechanism in the pure-theorem checker;
[surface-substitution-capture.md](surface-substitution-capture.md) is capture
in a different substitution.
