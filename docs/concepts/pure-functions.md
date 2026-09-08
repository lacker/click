# Pure Click functions

Pure Click functions compute specification values. They do not run as C code.

For example, the standard library defines `count`:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

This function counts occurrences in a range of an array-ref parameter.

Pure Click functions can use immutable `let` bindings:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function inc_with_let(x: int32) -> int32 {
    let next: int32 = x + 1;
    next
}
```

The annotation is optional when the value's type is already clear:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
let next = x + 1;
```

## Functions versus predicates

A pure Click function returns a value:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function count(...) -> int32 { ... }
```

A predicate returns a proposition:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}
```

Use functions for reusable computed values. Use predicates for reusable facts.

## Array refs

When a pure Click function takes `int32 p[]` or `uint8 p[]`, the parameter is a
specification-level array ref. It contains:

- a memory snapshot,
- a pointer,
- and an element type.

That is why this postcondition works:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
ensures permutation(p, old(p), 0, n) by auto;
```

The first `p` means the current array. `old(p)` means the function-entry array
at the same pointer.

## Folds

Range folds express computations over ranges:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
(lo..hi).fold(init, |acc, k| {
    ...
})
```

The kernel has selected reasoning support for the current standard-library
folds, especially `count` and `permutation`. It is not yet a general induction
engine for arbitrary folds.

## Well-founded recursion

A pure function may recurse when it declares a checked measure. Integer
recursion uses a nonnegative, strictly decreasing `int32` parameter:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

Unlike a C contract, a pure function denotes a value and must be total. Click
therefore checks every call inside a direct or mutual recursive component. On
each reachable recursive edge, the callee measure must be nonnegative and
strictly smaller than the caller measure. A path that makes no recursive call
does not need a nonnegative incoming measure, so the example returns `0` for a
negative argument without recursing.

Recursive algebraic datatypes provide a second checked measure. After an
exhaustive match on the measure, a recursive call may pass an algebraic field
bound by that arm:

<!-- verified-example: mdtests/algebraic_structural_recursion.md -->
```click
function example_list_length(xs: List<int32>) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) => 1 + example_list_length(tail),
    }
}
```

The checker follows further exhaustive matches on already-smaller fields, so
nested descent is accepted. Multiple recursive fields and mutually recursive
datatype/function groups use the same rule. Matching an unrelated value does
not establish descent, and neither aliases nor arbitrary algebraic expressions
are guessed to be subterms.

The integer rule deliberately remains easy to audit: its recursive components
use only `int32` parameters and results, and a decreasing call is written as
the measure minus a positive constant (or as a smaller nonnegative constant)
under an explicit comparison guard. Lexicographic measures and recursive
array summaries are not yet supported.

All calls remain symbolic logical applications. An explicit `unfold` exposes
one defining equation and preserves the next unknown-depth call as an opaque
pure-function application, even when the selected call has constructor or
constant arguments. The same application is structurally equal to itself, but
Click does not recursively normalize it by an arbitrary depth budget.

## Proving recursive results

`decreases` establishes that a recursive definition denotes a value. It does
not prove every property of that value. Use explicit strong induction in a
pure theorem when the proof needs the result at a smaller argument:

<!-- verified-example: mdtests/pure_induction_countdown.md -->
```click
theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(countdown(n));
            normalize() using { n <= 0; }
        } else {
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1) == 0);
            normalize();
        }
    }
}
```

Pure conditional expressions remain symbolic during lowering, even when a
branch condition is available. Here `normalize() using { n <= 0; }` explicitly
checks the base-case reduction.

`induct(n) as ih` is a simple tactic. It requires the current
facts to prove `n >= 0`. Within the rest of that theorem proof, `ih(m)` states
the same goal at any proved nonnegative `m < n`. The application also requires
the theorem's declared requirements with `n` replaced by `m`; Click never
drops a domain condition merely because it is doing induction.

Bare `apply(ih(m))` is smart because it plans explicit proofs of those fixed
obligations. Expansion ends in `apply(ih(m)) using { ... }`, the simple form
that checks exactly the listed obligations without searching.

The induction variable must currently be an `int32` theorem parameter. Other theorem
parameters remain fixed, so `ih` takes only the replacement value for the
named induction parameter. This is strong induction, so calls such as
`ih(n - 2)` are supported when the branch facts prove the argument is
nonnegative and smaller. The local hypothesis is not a global theorem and is
not available in C execution proofs.

For a recursive algebraic parameter, constructor-branching `induct` combines
exhaustive case analysis with structural induction:

<!-- verified-example: mdtests/algebraic_structural_induction.md -->
```click
induct(xs) as ih {
    List::Nil => {
        // base case
    }
    List::Cons(head, tail) => {
        apply(ih(tail));
        // inductive case
    }
}
```

Every constructor must appear exactly once with its exact field arity. Pattern
bindings exist only inside their arm. The local hypothesis may be instantiated
at each immediate field of the same recursive datatype; a binary-tree node
therefore supplies hypotheses for both children. The theorem's other
parameters stay fixed, and its requirements are substituted and checked at
the chosen child just as for integer induction. Mutual induction across
different datatype families is not yet generated.

Expression-level `match` remains symbolic and does not itself split a proof or
introduce proof-scope names. Only the explicit constructor-branching induction
form performs proof case analysis.

`unfold(function(args))` explicitly exposes one symbolic defining equation.
A recursive call produced by that layer stays opaque. Neither `simp` nor
repeated evaluation silently starts induction or unfolds to a depth limit.
Pure theorem induction is also unrelated to a C function's optional
termination evidence: it proves a proposition about specification values, not
that a C call returns.

## When to use pure functions

Use a pure Click function when:

- a property depends on a computed summary,
- a predicate would otherwise duplicate logic,
- or a standard library concept should be written in Click rather than
  hard-coded into the kernel.

If a function becomes hard to prove, the missing piece might be a general proof
rule, a better predicate abstraction, or a simpler library definition.
