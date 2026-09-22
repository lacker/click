# reachability needs an algebraic loop witness

Classification: **missing proof-language representation**.

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
