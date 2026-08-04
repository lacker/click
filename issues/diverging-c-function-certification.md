# Certify C functions that may or must diverge

## Dependency

Do this after
[the partial-correctness kernel boundary](partial-correctness-kernel-boundary.md)
exists. Otherwise accepting a function with no return frontier risks turning a
vacuous postcondition into a false concrete-execution theorem.

## Problem

Opaque contract certification currently requires a nonempty “complete
execution frontier.” Annotated loop verification attempts to produce an exit
branch and emits a `loop exit reachability` obligation when no such branch is
available. Consequently a safe function containing `while (1)` cannot receive
a verified contract rule.

This rejects ordinary C designs such as event loops, stream processors, worker
threads, and functions that wait indefinitely for a condition. It also obscures
the intended meaning of loop invariants: invariants prove safety across every
finite iteration prefix; they do not prove progress toward an exit.

## Desired behavior

Function certification must account for three kinds of behavior separately:

- returning paths, which must satisfy effects, returned-resource guarantees,
  and every `ensures` clause;
- finite bad paths, including undefined behavior and modeled runtime contract
  errors, which must be rejected; and
- infinite paths, for which return postconditions are inapplicable but every
  finite prefix must remain safe.

A verified, preserved constant-true loop may therefore yield no successor at
the function's return frontier without making certification fail. Body-safety
evidence should come from initialization, one-iteration preservation, call
contracts, and absence of finite bad paths—not from the existence of a return.

It is mathematically correct for an always-diverging function to satisfy
`ensures false`: the postcondition is conditional on returning. Preserve this
as a high-signal semantic regression test, while documenting it in kernel or
advanced material rather than presenting it as normal authoring style.

Resource behavior needs the same distinction. A callee that never returns does
not return its owned inputs to the caller, because the caller never resumes.
The callee must nevertheless maintain enough resource authority to verify every
finite step of its own execution. Loop invariants and recursive call contracts
are the relevant boundaries.

## Suggested implementation shape

- Let a verified loop preservation certificate represent zero possible exits
  when the guard is provably always true.
- Do not synthesize an impossible exit plus a false “reachability” obligation.
- Let function certification succeed with zero return paths when body safety
  has been established by the verification structure.
- Check `ensures`, return-resource, and endpoint effect claims over return paths
  only. Check write-footprint claims and resource authority over every finite
  body step, including steps on paths that do not return. Do not mistake an
  empty return set for an unchecked proof.
- Keep safety obligations non-vacuous: a zero-return function still needs a
  complete safety argument for its loop bodies and calls.
- Make proof tactics that genuinely require a function-exit frontier report
  that the verified function has no return path, rather than claiming contract
  certification itself failed.

The implementation does not need to enumerate or construct an infinite trace.
Inductive safety over all finite prefixes is enough for this issue.

## Focused mdtests

Add small tests with explicit names and purposes:

- `infinite_loop_partial_contract.md`: safe `while (1)` with a preserved
  invariant passes without a return frontier.
- `infinite_loop_vacuous_ensure.md`: the same function can partially establish
  `ensures false` without establishing termination.
- `infinite_loop_rejects_undefined_behavior.md`: division by zero or another
  immediate finite bad step inside the loop still fails.
- `may_diverge_ensure_on_return.md`: a function such as
  `wait_while_nonzero(int32 *flag)` loops forever when the stable input cell is
  nonzero and returns when it is zero; its return postcondition is checked only
  on the exit case.
- `infinite_loop_resource_invariant.md`: an owned composite resource survives
  each loop iteration even though it is never returned to a resumed caller.
- `caller_after_partial_call.md`: code after a possibly divergent call is
  verified under the callee's postcondition on the hypothetical return branch,
  without producing a termination theorem.

Include a negative kernel test proving that the first two mdtests cannot be
reinterpreted as `CFunctionExecutes(... Return ...)`.

## Documentation

In addition to the semantic documentation in the dependency issue:

- explain that an invariant proves safety and exit facts, not eventual exit;
- explain why a caller may reason from a postcondition after a call even though
  the call may never return; and
- identify liveness and productivity as unsupported, separate properties.

## Acceptance criteria

- Safe functions with no return frontier can be verified and used modularly.
- Finite undefined behavior remains rejected inside indefinitely running code.
- `ensures` and returned resources are checked exactly on returning paths.
- Resource authority and declared write footprints remain enforced on finite
  prefixes of divergent paths.
- Loop verification no longer invents an exit-reachability obligation merely
  because the loop is perpetual.
- Focused mdtests and kernel tests cover definite divergence, possible
  divergence, safety failure, resources, and callers.
