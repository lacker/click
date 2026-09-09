# Reject writes from contracts without an effect clause

**Severity: critical.** A contract with no function-level `immutable` or
`mutable` clause must not let callers preserve memory across a callee that
writes it.

## Violated invariant

An omitted function-level effect clause denotes an empty externally visible
write footprint. A verified function rule may preserve caller memory only when
the callee's certified effect claim covers the memory it writes. A frame
derived from owned resource transfer remains an explicit resource transition,
not an empty effect clause.

## Regression

`mdtests/call_without_effect_clause_rejected.md` verifies the minimal case:

```c
int32 g = 0;

int32 bump() {
    g = g + 1;
    return 0;
}
```

```click
verifying "call_without_effect_clause_rejected.c";

int32 bump() {
    requires g < 100;
    ensures result == 0;
}
```

The contract must be rejected at `bump`'s store with an outside-the-footprint
diagnostic. It must not be accepted and then used by a caller as if `g` were
unchanged.

## Acceptance criteria

- A missing effect clause is checked as an empty footprint during contract
  certification.
- The rejection identifies the callee write and its empty evaluated footprint.
- A read-only function with no effect clause still verifies.
- A callee with `mutable &g[0..1]` can be called by a caller that declares the
  same mutable footprint and states the resulting value.
- A caller declaring `immutable` or omitting its own effect clause is rejected
  when the callee's certified effect changes `g`.
- Resource-derived mutable frames continue to be checked by resource
  transitions and do not acquire a synthetic surface effect clause.
- The contract reference documents that omitting an effect clause means an
  empty footprint, alongside `immutable` and `mutable`.
