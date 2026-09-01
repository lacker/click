# Allow memory reads in `requires` propositions

Found by the 2026-09-01 kernel audit at cb034b21.

Any indexed read inside a `requires` proposition, including under `forall`,
is rejected by `src/surface/lowering/proposition_lowering.rs:480-482`
(`ContractExpression::Index(_, _) => Err("memory reads are not supported in
`requires` propositions yet")`). Field reads (`obj->len`) and `*p` dereferences already lower in `requires`
(`proposition_lowering.rs:387-390`, `:663-675`); only the `Index` arm is
rejected. Quantified preconditions about array contents (sortedness, null
termination) therefore cannot be stated; they must be encoded as resources or
predicates or moved to a callee's ensures.

## Violated invariant

A precondition should be able to state facts about the memory the function
is given, over the entry snapshot, with loadability discharged from the
function's resource requirements.

## Intended regression

Mdtest: `int32 first(int32 a[], int32 n) { return a[0]; }` with `requires
1 <= n; views a[0..n]; requires a[0] == 7; ensures result == 7;`. A second
with `requires forall (k: int32) { 0 <= k and k < n - 1 implies a[k] <= a[k +
1] }` used by a binary search. A negative mdtest shows a `requires` reading
outside the declared view fails with a loadability diagnostic.

## Acceptance criteria

- Requirement lowering accepts `Index` (`a[k]`) reads against the entry
  memory the way `->` field reads and `*p` already are, emitting loadability
  obligations discharged from resource requirements.
- The entry facts are available to the body proof and to callers proving the
  precondition.
- The tests above pass; `scripts/check.sh` passes.
