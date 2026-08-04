# Verify recursive C functions by contract

## Dependencies

Implement this after partial-correctness summaries are distinct from concrete
execution and functions with no guaranteed return can be certified. Recursive
C calls must not require termination evidence.

## Problem

Click's verified-call environment is currently built in verification order.
An unresolved callee is an error, and a function's own verified rule is not
available while its body is checked. Direct and mutual C recursion therefore
cannot be verified modularly.

Simply installing the finished rule early would be circular and forgeable.
Requiring a decreasing measure would avoid some cycles but incorrectly reject
safe C functions that may intentionally run forever.

## Proof rule

Use the standard partial-correctness recursion rule:

1. Compute strongly connected components of the C call graph.
2. For one recursive component, create scoped *provisional contract
   hypotheses* for every member. These are not globally usable verified rules.
3. Verify each exact function body under the hypotheses for calls within the
   component and ordinary verified rules for calls outside it.
4. Require body safety, effects, resources, and postconditions to certify for
   every member.
5. Only after the whole component succeeds, atomically package and publish the
   real verified rules. If any member fails, publish none of them.

This is sound without a decreasing measure. Any terminating execution has a
finite recursive call tree. Induction on that tree's maximum call depth
justifies each use of the provisional contract. An infinite recursive execution
has no return postcondition to establish, while any undefined behavior would
occur at some finite depth and remains a safety failure.

That finite-call-depth argument should be recorded in `docs/kernel.md` and in
comments at the kernel constructor that closes a recursive component. Avoid
describing the rule only as “assuming the function's own contract,” which hides
the reason the circular-looking rule is valid.

## Resources and effects

Recursive hypotheses must use exactly the same resource-transfer and effect
checks as ordinary opaque calls:

- requirements and owned resources transfer into each recursive call;
- returned resources and `ensures` facts become available only on its
  hypothetical return branch;
- a divergent recursive call does not give resources back to unreachable
  continuation code;
- recursive composite resources may be unfolded only through their existing
  guarded resource rules; and
- mutation footprints are checked at every finite call boundary.

Do not add an “inline recursive body until the budget runs out” fallback. It is
neither modular nor a proof rule.

## Surface design

Partial recursive C functions should need no recursion keyword and no
`decreases` clause. Ordinary contracts already contain the required proof
interface. Source order should not matter within or between call-graph
components.

Optional termination annotations belong to the separate termination issue.
Their absence must never be diagnosed as a failure to verify an otherwise
valid recursive C contract.

## Focused mdtests

- `recursive_c_base_case.md`: direct recursion with a returning base case and
  a simple arithmetic postcondition.
- `recursive_c_may_diverge.md`: a recursive branch may call itself without
  decreasing; partial safety and its return postcondition still verify.
- `recursive_c_vacuous_return.md`: a function that assigns the result of `f()`
  to a local and immediately returns that local can satisfy a partial return
  postcondition but produces no termination evidence.
- `recursive_c_rejects_bad_step.md`: undefined behavior before a recursive call
  is rejected.
- `recursive_c_resources.md`: a linked-list traversal transfers a guarded
  recursive resource through the recursive call and returns it on the base and
  returning recursive paths.
- `mutual_recursive_c_functions.md`: an even/odd-style pair verifies as one
  component regardless of declaration order.
- `recursive_component_is_atomic.md`: one invalid member prevents every rule
  in its component from being published.
- `recursive_c_calls_verified_helper.md`: a recursive component can call an
  already verified nonrecursive helper normally.

Add kernel tests showing that provisional hypotheses cannot escape their
component and cannot be supplied through a public execution environment.

## Acceptance criteria

- Direct and mutual recursive C functions verify by exact contracts.
- C recursion is partial-correctness by default and has no mandatory decrease.
- Source order no longer determines whether a recursive component is
  resolvable.
- Component publication is atomic and kernel-controlled.
- Recursive calls preserve the existing opaque-call resource, effect, and
  certificate-replay guarantees.
- Tests distinguish a partial recursive contract from a termination proof.
