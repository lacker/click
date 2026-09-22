# reachability needs an algebraic loop witness

Classification: **algebraic witness representation fixed; snapshot transport remains**.

The first missing layer now has positive checked regressions:
`mdtests/algebraic_existential_witness.md` removes DFS, arrays, and C
execution, while `mdtests/algebraic_existential_loop_witness.md` carries a
changing witness through a loop. The proposition

```click
exists (fuel: Nat) { fuel == Nat::Zero }
```

has the immediate witness `Nat::Zero`; algebraic `forall`, `exists`,
`witness`, `choose`, and `choose(... from invariant N)` now support it.

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

The obvious existential invariant is now representable. In the complete
search, the store to `visited[cur]` advances the current memory snapshot. A
chosen fact for `walk(next, from, fuel) == cur` still names `next` at the
iteration-entry snapshot, while unfolding the successor witness after the
store names `next` at the current snapshot. Although `next` and `visited` are
declared separate and `next` is only viewed, the recursive pure-function
equality is not transported between those snapshots. That is the remaining
direct blocker.

Numeric fuel still does not replace the witness because a recursive pure
function with an array argument is refused:

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

## Implemented algebraic witness layer

The implementation extends the existing quantifier machinery rather than
adding DFS-specific model state or a new ghost-resource convention:

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

The first three acceptance layers now pass: the `Nat::Zero` witness, a pure
choice reused beneath `Nat::Succ`, and a loop using
`choose(... from invariant 0)`. The remaining `walk` layer should retain the
same C and invariant while repairing snapshot-stable transport; it must not
specialize the function or move the witness into C.
