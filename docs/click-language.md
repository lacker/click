# Click Language

Click files are sidecar specifications for C0 sources.

## File Shape

```click
verifying "file.c";

int32 function_name(int32 p[], int32 n) {
    requires n >= 0;
    requires valid_range(p[0..n]);
    ensures label: result == n by auto;
}
```

`verifying "file.c";` names a C source supplied to the verifier. Function
signatures in the `.click` file are checked against the parsed C0 source.

Each `ensures` clause is a separate guarantee. A guarantee may be labeled with
`label:`. Omitting a proof clause uses the default prover, currently `auto`.

## Requirements

Requirements are shared by all guarantees for the function.

Supported structural requirements:

```click
requires valid_range(p, 12);
requires valid_range(p[0..n]);
requires valid_range((p + 1)[0..1]);
requires disjoint(dst[0..n], src[0..n]);
```

`valid_range(base[start..end])` and `disjoint(left[start..end],
right[start..end])` use half-open `int32` element ranges. This `..` syntax is
Click contract syntax, not C expression syntax.

`requires` can also use Click propositions, but direct memory reads in
requirements are intentionally limited. If a precondition needs memory reads,
package it as a named predicate and unfold it at proof sites when needed.

## Propositions

Click proposition connectives are words:

```click
result == x and not (result != x)
result == x implies result >= 0
forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) }
```

Do not use C logical operators such as `&&`, `||`, or `!` in Click
propositions. Those remain C expression syntax.

Range proposition helpers:

```click
(lo..hi).all(|k| { p[k] <= x })
(0..3).any(|k| { p[k] == x })
```

`.all` lowers to a bounded universal proposition. `.any` currently requires
concrete bounds and unrolls to a finite disjunction.

## `old(...)`

`old(expression)` evaluates a contract expression in the function-entry state.
It is mainly used in postconditions and invariants:

```click
ensures p[0] == old(p[0]) by auto;
ensures forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) } by auto;
```

Inside `old(...)`, `result` is unavailable.

When `old(p)` is passed as an array argument to a pure Click function or
predicate, it becomes an entry-state Click array ref. For example,
`permutation(p, old(p), 0, 2)` compares post-state `p` to entry-state `p`.
See [click-core.md](click-core.md).

## Pure Click Functions

Click functions are specification-level value definitions, not executable C
functions.

```click
function inc(int32 x) -> int32 {
    x + 1
}

function eq_as_int(int32 x, int32 y) -> int32 {
    if x == y { 1 } else { 0 }
}

function count3(int32 p[], int32 x) -> int32 {
    let initial = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

Supported expression features include parameters, literals, `+`, `-`, indexing,
`let name = value; body`, `if proposition { then } else { else }`, range
`.fold`, and calls to other non-recursive Click functions. Recursive Click
functions are rejected.

In pure Click function parameters, `int32 p[]` and `int32* p` are treated as
array-ref parameters. Indexing `p[k]` loads from the memory snapshot carried by
that argument. This is why `count(p, ...)` can be called with either current
`p` or `old(p)`.

Concrete folds are unrolled. Symbolic folds remain `RangeFold` value terms in
the megakernel and can be reasoned about by supported fold laws.

## Predicates

Predicates return Click propositions:

```click
predicate sorted_range(int32 p[], int32 lo, int32 hi) {
    forall (int32 i) {
        forall (int32 j) {
            lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}
```

Predicate calls are opaque by default. Requirements and loop invariants can
reuse exact predicate facts, but Click does not unfold predicate bodies unless a
proof asks for it:

```click
ensures sorted: sorted_range(p, 0, n) by {
    symbolic_execute();
    unfold(sorted_range);
    simp();
    close();
}
```

In loop invariants, an unfold-only proof block exposes predicate bodies before
the loop verification condition is generated.

Like pure Click functions, predicate array parameters are Click array refs.
A predicate can compare two arrays from different memory states when its caller
passes arguments such as `p` and `old(p)`.

## Effects

Function-level effects are separate from postconditions:

```click
immutable by frame;
mutable p[0..n] by frame;
mutable dst[0..n], counter[0..1] by frame;
```

`immutable` proves there are no externally visible memory writes. `mutable`
states an upper bound on externally visible writes. It does not claim every
listed cell changes.

Loop-level and step-level effects are described in [proof-workflow.md](proof-workflow.md)
and [memory-model.md](memory-model.md).
