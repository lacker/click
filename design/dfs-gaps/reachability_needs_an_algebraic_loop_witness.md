# reachability needs an algebraic loop witness

Classification: **missing proof-language representation**.

The first missing layer now has a checked minimal reproduction:
`mdtests/algebraic_existential_witness_rejected.md`. It removes DFS, arrays,
and C execution entirely. The proposition

```click
exists (fuel: Nat) { fuel == Nat::Zero }
```

has the immediate witness `Nat::Zero`, but parsing stops at `Nat` with
`quantifier type must be a C type or Integer`. This is the smallest failure;
the loop below needs the same proposition plus elimination of its witness at
the next iteration.

The direct correctness invariant for the fixed search C is:

```click
function walk(next: int32[], from: int32, fuel: Nat) -> int32
    decreases fuel
{
    match fuel {
        Nat::Zero => from,
        Nat::Succ(previous) => next[walk(next, from, previous)],
    }
}
```

At each loop head, some `fuel` witnesses
`walk(next, from, fuel) == cur`. The initial witness is `Nat::Zero`; after
`cur = next[cur]`, the witness is `Nat::Succ(fuel)`. Both defining equations
and their array-read obligations verify in isolation. The missing part is a
sound way to carry that changing algebraic witness through the loop.

The obvious existential invariant is not available: kernel existentials cover
`int32`, `Integer`, and pointers, but not algebraic types such as `Nat`. Numeric
fuel does not replace it because a recursive pure function with an array
argument is refused:

```text
recursive pure function `follow_i32` currently supports only int32 parameters
and an int32 result
```

Deriving a unique witness from the existing `Integer` termination measure is
also blocked. After the point update, arithmetic proves the new path length is
the old length plus one, but Click cannot rewrite that `Integer` equality
under `to_nat(...)` to establish
`to_nat(new) == Nat::Succ(to_nat(old))`. Even after applying both checked
round-trip laws, `simp() using` leaves the algebraic equality open; `rewrite`
refuses because it only accepts a 32- or 64-bit machine-integer equality in an
algebraic goal.

A field-bearing ghost resource can physically carry a `Nat`, but putting the
actual reachability relation in that resource is rejected:

```text
resource `search_path` fact cannot use recursive function `walk`
```

An empty token plus a separate loop invariant can be forced farther by
matching and rebuilding the token on every iteration. That exports verifier
bookkeeping as a produced function resource solely to state ordinary graph
reachability, so it is not an acceptable proof of the intended C interface.

Intended regression: permit an algebraic witness in a loop proposition (or an
equivalent first-class ghost binding) so the invariant above initializes with
`Nat::Zero`, preserves with `Nat::Succ(fuel)`, and the success return exposes
the witness without changing the C or manufacturing a resource token.

## Smallest sound implementation

Extend the existing existential machinery rather than adding DFS-specific
model state or a new ghost-resource convention:

1. Permit algebraic `ClickType` binders in `forall` and `exists`, lower them
   through an algebraic specification proposition to the kernel's existing
   `Sort::Algebraic(type)` proposition binder, and retain the type on the
   binder.
2. Generalize `witness(name = value)` to evaluate an algebraic expression and
   substitute its checked algebraic term into that binder. The kernel already
   represents algebraic variables and generic existential sorts; the missing
   restriction is primarily in the surface/specification bridge and the
   tactic adapter.
3. Generalize `choose` in the other direction, placing a fresh algebraic term
   in the proof-local algebraic environment. For loops, add an explicit
   `choose(name from invariant N)` source (or an equivalent named-invariant
   source), because today's `choose` can only open function requirements.

The implementation should be accepted in layers: first turn the checked
`Nat::Zero` reproduction into a passing witness proof; then add a pure theorem
that chooses `fuel` from an algebraic existential and returns
`Nat::Succ(fuel)` as a new witness; then a one-counter loop using
`choose(... from invariant 0)`; finally the DFS `walk` invariant. This keeps
the new rule general, kernel-checked, and independent of array reachability.
