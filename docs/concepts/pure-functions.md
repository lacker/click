# Pure Click functions

Pure Click functions compute specification values. They do not run as C code.

Machine scalar arguments use the declared parameter type. A call and its
unfolded body apply the same native conversion, including any narrowing
bounds. Thus an unsuffixed `0` passed to a `uint64` parameter denotes the same
argument as a `uint64` value proved equal to zero.

For example, this function counts the occurrences of `x` in the first three
cells of an array-ref parameter:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function count3(p: int32[], x: int32) -> int32 {
    let initial = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

The standard library's `count(p, lo, hi, x)` is the same fold over a symbolic
range `lo..hi` (see
[`library/permutation.click`](https://github.com/clicklang/click/blob/master/library/permutation.click)).

Pure Click functions can use immutable `let` bindings:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
function inc_with_let(x: int32) -> int32 {
    let next: int32 = x + 1;
    next
}
```

The annotation is optional when the value's type is already clear:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
let initial = 0;
```

## Pointer results

A pure function can return a pointer, including one selected from a model:

<!-- verified-example: mdtests/pure_pointer_result.md -->
```click
function identity(p: int32*) -> int32* { p }
```

The result stays opaque until `unfold(identity(p))` establishes its defining
equation. It retains its pointer type and arguments, and equality rewriting
can enter nested calls. Returning a pointer grants no ownership of the memory
it names and does not make it distinct from other pointers.

## Functions versus predicates

A pure Click function returns a value:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function count3(...) -> int32 { ... }
```

A predicate returns a proposition:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
predicate one_more(x: int32, y: int32) {
    inc(x) == y
}
```

Use functions for reusable computed values. Use predicates for reusable facts.

## Array refs

When a pure Click function takes `p: int32[]` or `p: uint8[]`, the parameter is a
specification-level array ref. It contains:

- the memory its reads are taken in,
- a pointer,
- and an element type.

That is why this postcondition, using the standard library's `permutation`
predicate (equal `count` of every value over `0..3`), works:

<!-- verified-example: mdtests/loop_stdlib_permutation_invariant.md -->
```click
ensures permutation_after_loop: permutation::permutation(p, old(p), 0, 3);
```

The first `p` means the current array. `old(p)` means the function-entry array
at the same pointer.

## Bodies read only their parameters

A body may name its parameters, its own `let`, fold and quantifier bindings,
and other pure functions. It may not read a C object by name: a file-scope
variable such as `counter`, or any object by its qualified `unit::counter`
form, is refused:

<!-- verified-example: mdtests/a_pure_function_reading_a_global_by_name_is_refused.md -->
```click
function read_counter(x: int32) -> int32 {
    counter + x
}
```

An application is a term over its argument values, and the only memory it
carries is the memory inside an array-ref argument. A body that read
`counter` directly would make `read_counter(0)` one term before and after a
store to `counter`, so a `requires` fact about it would prove a false
`ensures`. Pass the value in instead; the application then says which value it
was applied to, and `old(...)` names the entry value as usual:

<!-- verified-example: mdtests/a_pure_function_takes_a_global_value_as_an_argument.md -->
```click
function read_counter(c: int32, x: int32) -> int32 {
    c + x
}

int32 bump() {
    owns counter;
    requires counter == 5;
    requires read_counter(counter, 0) == 5;
    ensures counter == 6;
    ensures read_counter(old(counter), 0) == 5;
}
```

The same rule applies to [predicate bodies](predicates.md#bodies-read-only-their-parameters).

## Folds

Range folds express computations over ranges:

```text
(lo..hi).fold(init, |acc, k| {
    ...
})
```

C-valued folds currently require `int32` bounds and an `int32` accumulator.
Other C carriers are rejected with a specific diagnostic. Folds with a mathematical
`Integer` accumulator support `int32`, `uint64`, or `Integer` bounds; their
item binder has the bounds' type. In particular, `uint64` bounds do not imply
a `uint64` accumulator.

The kernel has selected reasoning support for the current standard-library
folds, especially `count` and `permutation`. It is not yet a general induction
engine for arbitrary folds.

## Well-founded recursion

A pure function may recurse when it declares a checked measure. Integer
recursion uses a nonnegative, strictly decreasing `int32` parameter:

<!-- verified-example: mdtests/pure_recursive_function.md -->
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
function example_list_length(xs: TestList<int32>) -> Integer
    decreases xs
{
    match xs {
        TestList::Nil => 0,
        TestList::Cons(head, tail) => 1 + example_list_length(tail),
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
        let ih = induct(n);
        if n <= 0 {
            unfold(countdown(n));
            close() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1), 0);
            close();
        }
    }
}
```

Pure conditional expressions remain symbolic during lowering, even when a
branch condition is available. Here `close() using { n <= 0; }` proves
the base case from the branch condition. The two `have`s state the hypothesis's
obligations at `n - 1` before `apply(ih(n - 1))` looks them up. They compare
`to_integer(n - 1)`, the `int32` value the hypothesis is instantiated at, not
the `Integer` difference that `0 <= n - 1` would state.

Click cannot yet represent a specification conditional that selects between
distinct pointer values with a symbolic guard. A comparison such as
`(if flag == 0 { p } else { q }) != 0` can be written as
`(flag == 0 and p != 0) or (flag != 0 and q != 0)`.

`let ih = induct(n)` is a simple tactic. It requires the current
facts to prove `n >= 0`. Within the rest of that theorem proof, `ih(m)` states
the same goal at any proved nonnegative `m < n`. The application also requires
the theorem's declared requirements with `n` replaced by `m`; Click never
drops a domain condition merely because it is doing induction.

`apply(ih(m))` checks those obligations against facts in scope. Establish a
missing one with `have` before the application. Expansion keeps the same
application.

The measure form's induction variable must be an `int32` or `uint64` theorem parameter. It
quantifies that one variable, so other theorem parameters remain fixed and
`ih` takes only the replacement measure. This is strong induction, so calls
such as `ih(n - 2)` are supported when the branch facts prove the argument is
nonnegative and smaller. A `uint64` measure is intrinsically nonnegative;
its hypothesis instead owes the strict unsigned decrease and the substituted
requirements. The argument keeps the measure's type, including values above
`INT32_MAX`. The local hypothesis is not a global theorem and is
not available in C execution proofs.

Fixed mathematical `Integer` parameters and requirements on them retain the
theorem's Integer bindings in the induction hypothesis. See
[`scalar_induction_keeps_fixed_integer_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/scalar_induction_keeps_fixed_integer_parameters.md).

For a recursive algebraic parameter, introduce the structural induction
hypothesis with `let ih = induct(xs);` and prove the constructor cases with
`match xs`. Helpers may precede the declaration, separate it from the match,
or continue the proof after the match. The match can also be inside a `have`
proof, while the declaration still targets the original theorem goal:

<!-- verified-example: mdtests/algebraic_structural_induction.md -->
```click
let ih = induct(xs);
match xs {
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
therefore supplies hypotheses for both children. Mutual induction across
different datatype families is not yet generated.

The structural hypothesis is the theorem generalized over its other
parameters, so it takes the complete parameter list in declaration order:

<!-- verified-example: mdtests/algebraic_structural_induction_generalizes_parameters.md -->
```click
apply(ih(tail, List<int32>::Cons(head, acc)));
```

Only the inducted position is restricted, and the kernel checks it: it must
name a field the current arm bound, of the datatype being inducted on.
Every other position may name any well-typed term. This is what a recursive
case that changes another parameter needs — an accumulator, or a zipper frame
that grows the focused subtree — because its residual goal is the theorem at a
smaller inducted argument and *different* other arguments. The requirements
are substituted and checked at exactly the arguments given, just as for
integer induction, so an instantiation the theorem's `requires` does not
support is refused.

Passing the inducted argument alone still means "every other parameter
unchanged", so `ih(tail)` and a complete list that repeats the other
parameters name the same instance.

[`examples/modeled-binary-tree`](https://github.com/clicklang/click/tree/master/examples/modeled-binary-tree)
proves `plug_inorder_transport` this way: in the `Context::Left` arm the goal
is the theorem for the enclosing frame `up` at two rebuilt subtrees, and the
proof writes `ih(up, HeapTree::Node(parent, value, a, sibling),
HeapTree::Node(parent, value, b, sibling))`.

Expression-level `match` remains symbolic and does not itself split a proof or
introduce proof-scope names. A proof-level `match` performs case analysis; after an induction declaration,
its immediate recursive fields also admit applications of the hypothesis.

`unfold(function(args))` explicitly exposes one symbolic defining equation.
A recursive call produced by that layer stays opaque. Neither `close()` nor
repeated evaluation silently starts induction or unfolds to a depth limit.
Pure theorem induction is also unrelated to a C function's optional
termination evidence: it proves a proposition about specification values, not
that a C call returns.

### Unfolding a fold-bodied function over a symbolic range

A function whose body is a range fold can summarize an array range.
`unfold(function(args))` opens the range-fold law selected by the available
range conditions, stated over that function call. Any remaining law guards
are ordinary obligations, so the proof uses the same syntax as other unfolds.

<!-- verified-example: mdtests/unfold_fold_function_empty_range.md -->
```click
function icount(p: int32[], lo: int32, hi: int32, x: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| {
        acc + to_integer(if p[k] == x { 1 } else { 0 })
    })
}
```

With `hi <= lo` established, the step opens `icount(p, lo, hi, x) == 0`. With
`lo <= hi - 1` and `hi - 1 < 2147483647` established, it opens
`icount(p, lo, hi, x) == icount(p, lo, hi - 1, x) + <the cell at hi - 1>`. Both
sides of that equation are the same function, so the shorter range is the term
an induction hypothesis already speaks about, and a range property follows by
the ordinary `induct(hi)` over a nonnegative `int32` parameter.

Two consequences are worth stating plainly. The body's memory reads stay inside
the declaration, where the caller's `viewable` premise covers them: the proof
site never writes `v[k]` at the fold's bound index, which a pure theorem cannot
lower. And the step is a derived use of the kernel's two fold laws, not a new
axiom — the defining equation and its predecessor instance are the law's own
premises, so nothing about the declaration is assumed twice. The append form
therefore requires the fold's end to be a parameter of the function that the
fold reads nowhere else; otherwise the shorter fold would not be that function
at a smaller endpoint.

## When to use pure functions

Use a pure Click function when:

- a property depends on a computed summary,
- a predicate would otherwise duplicate logic,
- or a standard library concept should be written in Click rather than
  hard-coded into the kernel.

If a function becomes hard to prove, the missing piece might be a general proof
rule, a better predicate abstraction, or a simpler library definition.
