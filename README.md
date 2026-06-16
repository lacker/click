# click

`click` is a new programming language.

Click's goal is to make it easy to prove things about programs in other
programming languages. Starting with C.

## Megakernel Theory

There's a traditional principle of theorem prover design that says you should
build a small, trusted kernel.

The rationale is that you want it to be really small to avoid bugs, and then
you prove things outward from there.

My theory is that for the task of "systems engineering theorem proving", this
is actually the wrong design.

It's actually a good idea to put a whole lot of stuff into the kernel.
The rationale is that it lets you develop faster.
It lets you put more powerful stuff in the kernel, and it makes performance
better.
These are all really important for the systems engineering questions that we
care about.
Like, can we formally verify the Linux kernel.

There's a serious tradeoff!
The downside is that you are more likely to have bugs in the kernel.
But, for our domain, this is not the most important problem.
We aren't concerned about like, the soundness of mathematics itself.
We are verifying code that is already supposed to work.
So if we do discover bugs in the kernel, we don't have a huge tower of false
statements.
It isn't going to lead to some sort of philosophical disaster.

Plus, we can always use other systems to prove the soundness of the megakernel
itself.
In fact, we should do that, eventually, with a number of differently
implemented, alternative theorem-proving systems.
That will increase trust in the megakernel.
But it just isn't the priority during development, for the Click kernel to be
simple.
It should be fast on big codebases.
It should be easy to use, in terms of, it should be really good at proving
things.
Those are the priorities.

In other words, we are happy to hardcode axioms and tactics
about int32, char*, and float64 into the kernel.

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
- A **proof** is a block or sequence of tactic calls that proves a theorem.

The current `.click` proof language has only one tactic, `auto`. It invokes the
megakernel's C symbolic-execution axioms and spec-checking axioms to prove the
named theorem block.

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
    returns_second {
        requires valid_range(p, 12);
        ensures result == 2;

        proof {
            auto;
        }
    }
}
```

The C0 signature in the `.click` file is checked against the C source and a
mismatch is reported directly. Each named theorem block has its own
requirements, one result-equality `ensures` clause for now, and one proof block.
That sidecar path parses C0 source, builds the requested initial memory, runs
native symbolic execution, checks the result clause, and packages the result as
a megakernel `CFunctionSpec` theorem.

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
    returns_zero {
        ensures result == 0;
        proof { auto; }
    }
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
memory-safety premises.

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
