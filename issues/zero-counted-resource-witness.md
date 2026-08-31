# Zero counted-resource consumption loses the empty-family witness

## Violated invariant

Consuming the complete quantity of a counted resource should leave a usable
zero population. A later contract that consumes `0 of resource(...)` must not
require a positive resource fact merely to establish that the family is empty.

Today, after a symbolic quantity `amount of slot(owner)` is consumed in full,
`observe(0 of slot(owner))` is rejected because the resource bucket has been
removed. A following call whose contract consumes a C expression proved equal
to zero then reports a missing resource fact.

## Intended regression

Use a three-call C pipeline, without changing the C:

1. produce `amount of slot(owner)`;
2. consume the same `amount of slot(owner)` and establish `owner->count == 0`;
3. call a function that consumes `owner->count of slot(owner)`.

The Click proof should be able to establish or observe the zero population
after step 2 and take step 3 without manufacturing a positive resource fact.

## Acceptance criteria

- The unchanged pipeline verifies with explicit simple resource operations.
- Consuming the last positive quantity either retains an indexed zero-family
  witness or `observe(0 of ...)` derives one without scanning unrelated
  resources.
- A negative regression still rejects observing a positive quantity after the
  resource was consumed.
- The update cost remains `O(log N + projections supported by the affected
  resource)` and has a deterministic scaling regression if representation
  changes are required.
