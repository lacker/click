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

- `Bv32Term`, `PtrOffsetTerm`, and `ConditionTerm`
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
symbolic-execution axioms and spec-checking axioms to prove the named guarantee.

## C0 Status

C0 is not a standard language name here; it is this repo's tiny C subset used
to drive the design. It currently supports:

- `int32` and `int32*`
- integer literals and variables
- signed comparisons and equality, returning `int32` `0` or `1` like C
- signed addition and subtraction, with signed-overflow UB
- local `int32` and `int32*` declarations
- assignment and sequencing
- `if` / `else` with C scalar truthiness
- `while`, currently concrete/budget-capped for execution, plus a native
  invariant-rule checker for symbolic preservation and exit facts
- `return`
- address-of lvalues
- pointer arithmetic for `int32*`
- loads and stores, including `p[i]` syntax for `int32*` indexing
- known function calls through a small `CFunctionEnv`

The memory model has named blocks with byte sizes. Concrete in-range loads and
stores discharge memory-validity obligations directly. Symbolic accesses can
also be discharged from valid-range facts plus simple index bounds such as
`0 <= i < n`. Out-of-range or unknown memory accesses become proof obligations
or UB depending on the execution path.

## Proof Surface

The primary proof engine today is the `auto` tactic backed by native symbolic
execution in the megakernel. The underlying axioms produce theorem objects for
expression evaluation, statement execution, function execution, and
function-spec satisfaction.

Symbolic execution is bounded by an explicit `ExecutionBudget`: expression
steps, statement steps, function calls, loop unrolls, and path count. Exhausting
that budget is a Click proof/executor failure, reported as an `ExecutionLimit`;
it is not modeled as C undefined behavior or as a C runtime error.

Function specs package:

- initial state
- arguments
- required propositions
- expected outcome

The spec prover checks that requirements are strong enough to leave no
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
bytes)` and signed integer comparisons over parameters and literals.
`ensures` supports comparisons between small C0 integer expressions over
`result`, parameters, literals, parentheses, `+`, `-`, and post-state
`p[i]` memory reads. Postconditions can use `old(expr)` to evaluate an
expression in the pre-call state, which supports first-frame claims like
`p[0] == old(p[0])`. `auto` checks each guarantee on every symbolic execution
path. That sidecar path parses C0 source, builds the requested initial memory,
runs native symbolic execution, checks the postcondition clause, and packages
the result as a megakernel `CFunctionSpec` theorem.

## Markdown Tests

End-to-end examples live in `mdtests/`. Each markdown test can include prose,
one or more C source blocks, one Click sidecar block, and an expected result:

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

The first memory-safety demo is `fill3(int32* p)`: it writes three consecutive
`int32` cells through `p[i]` in a loop and reads back the final cell. With a
12-byte backing block, the megakernel proves the execution without leftover
memory-safety premises. The sidecar can also prove post-state memory
guarantees such as `ensures p[2] == 2 by auto;` and simple preservation
guarantees such as `ensures p[0] == old(p[0]) by auto;`.

## Near-Term Roadmap

1. Split `src/megakernel.rs` into smaller modules without changing semantics.
2. Expand the `.click` sidecar language just enough to express more realistic
   C specs: named preconditions, multiple ensures clauses, and simple symbolic
   arguments.
3. Add richer C integer coverage: unsigned operations, more widths, casts, and
   promotion rules.
4. Improve loop verification beyond concrete fuel-capped execution by making
   invariants useful from `.click`.
5. Grow memory reasoning toward real local arrays, pointer ranges, and frame
   conditions.
6. Replace the toy C0 parser with a path toward real C parsing when the proof
   model is ready for it.

## Verification

Run the test suite with:

```sh
cargo test
```
