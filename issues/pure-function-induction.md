# Add explicit induction for pure Click theorems

## Dependency and scope

Well-founded pure Click functions can already evaluate concrete calls and
expose one symbolic defining equation. The missing operation is proving a
general theorem about all values of a measure. This is a pure theorem feature,
not a C execution tactic and not C termination evidence.

Implement it after the recursive example work so that resource/call cleanup is
not mixed with a new logical rule. It is independent of structural C
termination once those boundaries are understood.

## Problem

Given:

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

Click can prove `countdown(3) == 0` by computation and can unfold
`countdown(n)` once. It cannot prove the general theorem
`n >= 0 implies countdown(n) == 0`, because the remaining symbolic recursive
application must stay opaque. Increasing an unfolding budget would be neither
a proof nor a termination argument.

## Proof rule, not function evaluation

Add explicit strong induction over the nonnegative `int32` values. The rule is
general: it proves a proposition `P(n)` and does not trust the implementation
of a particular recursive Click function. Current expression lowering exposes
one defining equation and leaves recursive re-entry opaque; induction supplies
the missing smaller-value fact without changing that evaluation boundary.

At a theorem claim with parameter `n`, requirements `R(n)`, and goal `P(n)`,
the induction step may assume a local hypothesis equivalent to:

```text
forall m: int32.
    0 <= m and m < n and R(m) implies P(m)
```

and must prove `P(n)` under the ordinary current assumptions, including
`R(n)` and `0 <= n`. The base case is not a separate axiom: when `n == 0`, the
strict-smaller hypothesis has no nonnegative instance.

Including the theorem requirements in the instantiated hypothesis is
essential. Assuming merely `P(m)` for every smaller `m` would be unsound when
the theorem is stated only on a restricted domain. To use the hypothesis at a
recursive argument, the proof must establish the requirements at that
argument.

Other theorem parameters remain fixed while `n` varies. A later generalization
may expose an explicit induction predicate or allow several varying parameters.

## Recommended surface shape

Use an explicit deterministic tactic that names its local hypothesis, for
example:

```click
theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            simp();
        } else {
            apply(ih(n - 1));
            simp();
        }
    }
}
```

The exact punctuation may follow parser constraints, but retain three visible
ideas: the induction variable, a named hypothesis, and explicit application at
a smaller value. Do not make `simp` silently start induction, and do not make
recursive evaluation repeat until a depth limit. If later experience calls for
an explicit pure-function equation tactic, design it separately; do not reuse
predicate/resource `unfold` ambiguously in this issue.

The first slice should allow induction only in a pure theorem claim whose
induction variable is an `int32` theorem parameter. A named induction
hypothesis behaves like a proof-local theorem and is available only inside the
remainder of that proof. It cannot escape into global theorem environments.

## Kernel boundary

Add a replayable derivation rule, conceptually
`StrongNonnegativeInt32Induction`, rather than certifying a tactic transcript by
trust. The kernel must check:

- the induction variable is the exact fresh symbolic theorem parameter;
- the current theorem claim and its requirements are abstracted
  capture-avoidingly into the induction predicate;
- the step derivation is checked under exactly the local smaller-value
  hypothesis;
- every hypothesis application instantiates the same predicate and proves
  `0 <= m`, `m < n`, and the substituted requirements;
- binder identities are fresh and cannot capture range, quantifier, or Click
  function binders; and
- the final derivation concludes the original exact goal.

The well-founded order is mathematical order on the finite set of nonnegative
`int32` values. Arithmetic used to construct a smaller argument must retain the
ordinary definedness and overflow obligations; induction does not grant
machine arithmetic for free.

The rule must not consult C termination maps, C call graphs, or recursive C
contract rules. Conversely, a theorem about a model used in a C postcondition
may be applied normally after it is independently certified.

## First supported slice

- Strong induction on one nonnegative `int32` theorem parameter.
- One theorem claim at a time, with its declared pure requirements included in
  the induction predicate.
- Other parameters fixed during induction.
- The existing one-equation lowering of direct or mutually recursive pure
  Click functions inside the step proof.
- A conjunction can express a mutual property if an even/odd-style example
  needs both functions; no separate mutually inductive theorem group yet.
- The induction tactic is deterministic and simple. Smart tactics may solve
  subgoals but may not invent the induction scheme.

Initially reject induction inside C execution proofs, resource transformations,
loop preservation proofs, and arbitrary nested `have` blocks. Those contexts
can be generalized after theorem-level proof replay is stable.

## Focused tests

- `pure_induction_countdown.md`: prove the general countdown result.
- `pure_induction_two_step.md`: a function recursing by two uses strong rather
  than predecessor-only induction.
- `pure_induction_preserves_requirements.md`: applying the hypothesis requires
  the theorem's domain assumptions at the smaller argument.
- `pure_induction_rejects_same_measure.md`: `ih(n)` is rejected.
- `pure_induction_rejects_larger_measure.md`: `ih(n + 1)` is rejected.
- `pure_induction_requires_nonnegative_domain.md`: an induction request with
  no proof that the current measure is nonnegative fails clearly.
- `pure_induction_is_explicit.md`: `simp` and repeated `unfold` do not acquire
  induction behavior.
- `pure_induction_mutual_conjunction.md`: prove an even/odd conjunction with
  one strong hypothesis, without adding a mutually inductive theorem group.
- Kernel tests reject mismatched predicates, captured binders, forged local
  hypotheses, and derivations whose step proves a different goal.
- Expansion/printing round-trips the induction syntax and replays the same
  kernel derivation without hidden smart search.

## Documentation

Update the pure-functions guide, proof-tactics reference, language reference,
kernel guide, and proof landscape. Show separately:

- `decreases` proves that a pure definition denotes a value;
- one-step `unfold` exposes its equation;
- `induct` proves a general theorem over a well-founded domain; and
- recursive C contracts and C termination use different judgments.

## Non-goals

- Automatic induction in `simp` or `auto`.
- Induction on C execution depth or C function bodies.
- Structural induction over recursive resources in this first issue.
- Lexicographic, transfinite, or user-defined well-founded relations.
- Coinduction, productivity, or stream properties.
- A general tactic language for inventing induction predicates.

## Acceptance criteria

- A general theorem about a symbolic recursive Click function verifies by an
  explicit, kernel-replayed induction rule.
- The local hypothesis is usable only at proved nonnegative smaller values and
  includes substituted theorem requirements.
- Same/larger instantiations, missing domain proofs, predicate mismatches, and
  binder-capture attempts are rejected.
- Recursive function evaluation remains one-step at symbolic arguments and
  never depends on an unfolding-depth budget.
- C recursion and C termination behavior are unchanged.
- Documentation consistently calls this pure theorem induction, not proof that
  a C call returns.
