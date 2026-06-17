# click

`click` is a new programming language.

Click's goal is to make it easy to prove things about programs in other
programming languages. Starting with C.

## Megakernel Theory

There's a traditional principle of theorem prover design that says you should
build a small, trusted kernel.

The traditional rationale is that to build a huge bug-free structure, you need the
heart of it to be bug-free. You can only do that by close inspection.
Close inspection is hard, so you want it to be really small.
Then you prove things outward from there.

I claim that for the task of "systems engineering theorem proving", this
is actually the wrong design.

Instead, you should put a lot of stuff into the kernel.
Call it a *megakernel*.
It is a good idea to have many data structures and axioms that are specific
to systems engineering.
The rationale is that it lets people develop faster.
It lets you put more powerful tactics in the kernel, and it makes performance
better.
These are important for the systems engineering questions that we care about.
Like, can we formally verify Linux.

There's a serious tradeoff!
The downside is that you are more likely to have bugs in the kernel.
But, for our domain, this is not the most important problem.
We aren't concerned about the soundness of mathematics itself.
We are verifying code that is already supposed to work.
When we discover bugs in the kernel, we don't have a huge tower of false
statements that we became dependent on.
It isn't going to lead to some sort of philosophical disaster.

We should certainly fix bugs in the kernel when we find them.
But it isn't the priority during development, for the Click kernel to be simple.
It should be fast on big codebases.
It should be powerful, ie, really good at proving things.
Those are the priorities.

In other words, we are happy to hardcode axioms and tactics
about char*, float64, or malloc into the kernel.

## Only humans may edit the content above this point. AIs may edit below this point.

## Architecture

The public crate currently exposes two top-level modules, with the C and Click
language support under `src/lang/`:

- `src/megakernel.rs`: megakernel axioms for systems-code reasoning. `Theorem`
  remains an abstract object; callers can inspect its proposition but cannot
  construct arbitrary theorems directly.
- `src/lang/c/`: a tiny C0 syntax importer. It parses a deliberately small C
  subset and lowers it to megakernel C functions/statements/expressions.
- `src/lang/click.rs`: a first `.click` sidecar verifier slice for C0.

The megakernel currently has native data structures for:

- `Bitvector32Term`, `PointerOffsetTerm`, and `ConditionTerm`
- C values, lvalues, expressions, statements, functions, and function
  environments
- local state and memory with explicit byte-sized blocks
- expression, statement, and function outcomes
- C undefined behavior and runtime errors
- propositions, assumptions, proof obligations, path facts, and theorems

`ConditionTerm` is a proof-level truth-valued term for path conditions,
overflow predicates, and range facts. It is not a C `bool`. Current C0
comparisons evaluate to `int32` `0` or `1`, matching C-style scalar truthiness.
Pointers are semantic objects with provenance blocks and pointer-offset terms;
they are not represented as C `int32` values. The current C0 target layout
still assumes 8-byte pointer objects; that should become explicit target
configuration when multiple ABIs matter.

C expression semantics distinguish lvalue evaluation from rvalue evaluation.
An lvalue identifies a C object, either a named local object or a memory object,
and rvalue evaluation reads from that object. This is the C-native basis for
`x`, `*p`, `p[i]`, assignment targets, and address-of expressions; it is also
the path toward real local array objects rather than treating arrays as secret
pointers.

## Proof Vocabulary

Click uses four core proof-system words:

- An **axiom** is a built-in trusted theorem-producing operation. In the Rust
  codebase, these are the megakernel functions that can construct a `Theorem`.
  Many of them are named `prove_*` because the name describes the theorem they
  produce, but in Click terminology they are axioms.
- A **theorem** is an abstract object representing a proven proposition. Users
  cannot construct arbitrary theorems directly.
- A **tactic** is a proof-language command that tries to prove a theorem or
  reduce a proof goal by invoking axioms and using existing theorems.
- A **proof** is a `by` clause: either one tactic call, or a block containing a
  sequence of tactic calls.

The current `.click` proof language has only one tactic, `auto`. Function
contracts attach `requires` clauses to the function and attach a `by` proof
clause to each `ensures` guarantee. An `ensures` clause can say `by auto;`, or
use block form `by { auto; }`. The tactic invokes the megakernel's C
symbolic-execution axioms and specification-checking axioms to prove the named guarantee.

## C0 Status

C0 is not a standard language name here; it is this repo's tiny C subset used
to drive the design. It currently supports:

- `int32` and `int32*`
- C-style `int32 p[]` / `int32 p[3]` function-parameter syntax, lowered to
  `int32*` like C
- integer literals and variables
- signed comparisons and equality, returning `int32` `0` or `1` like C
- signed addition and subtraction, with signed-overflow undefined behavior
- local `int32` and `int32*` declarations
- assignment and sequencing
- `if` / `else` with C scalar truthiness
- `while`, currently concrete/budget-capped for execution, plus a native
  invariant-rule checker for symbolic preservation and exit facts
- `return`
- address-of lvalues
- pointer arithmetic for `int32*`
- loads and stores, including `p[i]` syntax for `int32*` indexing
- known function calls through a small `CFunctionEnvironment`

The memory model has named blocks with byte sizes. Concrete in-range loads and
stores discharge memory-validity obligations directly. Symbolic accesses can
also be discharged from valid-range facts plus simple index bounds such as
`0 <= i < n`. Out-of-range or unknown memory accesses become proof obligations
or undefined behavior depending on the execution path.

## Proof Surface

The primary proof engine today is the `auto` tactic backed by native symbolic
execution and a first loop verification-condition path in the megakernel. The
underlying axioms produce theorem objects for expression evaluation, statement
execution, function execution, loop-invariant checking, and
function-specification satisfaction.

Symbolic execution is bounded by an explicit `ExecutionBudget`: expression
steps, statement steps, function calls, loop unrolls, and path count. Exhausting
that budget is a Click proof/executor failure, reported as an `ExecutionLimit`;
it is not modeled as C undefined behavior or as a C runtime error.

Function specifications package:

- initial state
- arguments
- required propositions
- expected outcome

The specification prover checks that requirements are strong enough to leave no
unresolved path facts or proof obligations and that execution reaches the
expected outcome.

The `.click` sidecar language is intentionally tiny. It currently supports this
shape:

```text
verifying "fill3.c";

int32 fill3(int32* p) {
    requires valid_range(p, 12);
    ensures returns_second: result == 2 by auto;
}
```

The C0 signature in the `.click` file is checked against the C source and a
mismatch is reported directly. Function-level `requires` clauses are shared by
all guarantees. Each `ensures` clause is a separately proven guarantee with its
own `by` proof clause. For now, `requires` supports `valid_range(pointer,
bytes)` with concrete byte counts or small byte-count expressions such as
`n * 4`, plus Click propositions over parameters and literals. `ensures`,
`assert`, and `invariant` clauses also use Click proposition syntax:

```text
result == x and not (result != x)
result == x implies result >= 0
forall (int32 k) { 0 <= k implies k >= 0 }
```

Logical structure uses Click words: `and`, `or`, `not`, `implies`, and
`forall`. C operators such as `&&`, `||`, and `!` remain C expression syntax
and are not reused as proposition connectives. Proposition comparisons embed
small C0 integer expressions over `result`, parameters, literals, parentheses,
`+`, `-`, and post-state `p[i]` memory reads. Postconditions can use
`old(expression)` to evaluate an expression in the pre-call state, which
supports first-frame claims like `p[0] == old(p[0])`. The parser and kernel
representation accept `forall (int32 name) { ... }`, but `auto` does not yet
prove useful quantified array-segment facts. `auto` checks each guarantee on
every symbolic execution path. That sidecar path parses C0 source, builds the
requested initial memory, first tries loop verification conditions for
annotated loops, checks the postcondition clause, and packages the result as a
megakernel `CFunctionSpecification` theorem. If the loop VC path cannot prove a
postcondition but leaves no invariant obligations, `auto` can still use bounded
execution for finite concrete-loop demos.

The sidecar also has first structural labels for intra-function proof
obligations:

```text
at statement 2 {
    assert i == 0 by auto;
}

at loop 0 {
    invariant i >= 0 by auto;
    invariant i <= 3 by auto;
}
```

`statement N` names the Nth source statement in structural order; `loop N`
names the Nth `while` loop. `assert` is a one-shot ghost check at the
structural target. `invariant` generates non-unrolling loop verification
conditions: entry checks, one-body preservation checks, and exit facts from the
invariant plus the false loop condition. Failed `auto` proofs report the
guarantee label, execution path, available requirements, path facts, and
remaining proof obligations.

The current loop VC path handles scalar loop locals by assigning fresh symbolic
values at the loop head. That is enough for proofs such as symbolic
`count_to_n(n)` with invariants `i >= 0` and `i <= n`, and symbolic pointer-loop
safety with `valid_range(p, n * 4)`. It also has a first frame rule for
memory-mutating loops: if the one-body symbolic write footprint is provably
distinct from a postcondition load, `auto` can prove that load equals
`old(...)`. Richer memory postconditions still need explicit memory invariants
and more general frame reasoning; the current fixed-size pointer demos continue
to use bounded execution for some final memory facts.

## Markdown Tests

End-to-end examples live in `mdtests/`. Each mdtest can include
prose, one or more C source blocks, one Click sidecar block, and an expected
result:

````text
```c filename=example.c
int32 example(int32* p) {
    return 0;
}
```

```click
verifying "example.c";

int32 example(int32* p) {
    ensures result == 0 by auto;
}
```

```expect
pass
```
````

Negative tests use `fail: expected diagnostic substring`. The Rust integration
test `tests/mdtests.rs` runs all `mdtests/*.md` files.

## Current Demo

The first memory-safety demos are fixed-size pointer loops:

- `fill3(int32* p)` / `fill3_array_loop(int32 p[3])` write three consecutive
  `int32` cells through `p[i]` and read back the final cell.
- `copy3(int32 dst[3], int32 src[3])` copies three cells from `src` to `dst`
  and proves `old(src[i])` postconditions.
- `count_to_n_loop_invariant(int32 n)` proves `result == n` for a symbolic loop
  bound using loop invariants instead of unrolling.
- `fill_n_symbolic_pointer_loop(int32 p[], int32 n)` proves symbolic pointer
  loop safety and `result == n` using `valid_range(p, n * 4)`.
- `fill_tail_preserves_first(int32 p[], int32 n)` proves a symbolic
  memory-mutating loop preserves `p[0]` while writing `p[i]` for `i >= 1`.

With 12-byte backing blocks, the megakernel proves these executions without
leftover memory-safety premises. The sidecar can also prove post-state memory
guarantees such as `ensures p[2] == 2 by auto;` and simple preservation
guarantees such as `ensures p[0] == old(p[0]) by auto;`.

## Near-Term Roadmap

1. Split `src/megakernel.rs` into smaller modules without changing semantics.
2. Expand the `.click` sidecar language just enough to express more realistic
   C specifications: named preconditions, multiple ensures clauses, structural `at`
   labels, and simple symbolic arguments.
3. Add richer C integer coverage: unsigned operations, more widths, casts, and
   promotion rules.
4. Extend loop verification from scalar locals to memory-changing loops with
   explicit memory invariants and frame reasoning.
5. Grow memory reasoning toward real local arrays, pointer ranges, and frame
   conditions.
6. Replace the toy C0 parser with a path toward real C parsing when the proof
   model is ready for it.

## Verification

Run the test suite with:

```sh
cargo test
```
