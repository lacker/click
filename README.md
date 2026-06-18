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

Click uses five core proof-system words:

- An **axiom** is a built-in trusted theorem-producing operation. In the Rust
  codebase, these are the megakernel functions that can construct a `Theorem`.
  Many of them are named `prove_*` because the name describes the theorem they
  produce, but in Click terminology they are axioms.
- A **theorem** is an abstract object representing a proven proposition. Users
  cannot construct arbitrary theorems directly.
- A **proof step** is a deterministic proof-language call that invokes an axiom
  or a fixed deterministic sequence of axioms.
- A **proof** is a `by` clause: either a replayable sequence of proof steps, or
  a tactic call that can later be expanded into proof steps.
- A **tactic** is a proof-language procedure that tries to generate a proof.
  Some tactics are deterministic; others, such as `auto`, may search. Proof
  steps should be stable and replayable.

The current `.click` proof language exposes tactic calls plus a first linear
proof-step script form. Function contracts attach `requires` clauses to the
function and attach a `by` proof clause to each guarantee. A proof clause can
say `by auto;`, `by simp;`, or `by frame;`, and can also use block form such as
`by { auto; }`. Deterministic replay scripts use function-call-shaped proof
steps:

```text
by {
    symbolic_execute();
    loop_vc(loop 0);
    frame(loop 0);
    simp();
    close();
}
```

This first proof-step slice uses an implicit proof state. `symbolic_execute`
builds the C0 symbolic verification paths. `bounded_execute()` runs the
deterministic bounded C0 executor for concrete-loop fallback proofs.
`loop_vc(loop N)` validates the named loop's generated verification conditions.
`frame(loop N)` validates and exposes the named loop's frame facts. `simp()`
asks the final close step to use deterministic simplification for the claim.
`close()` must be the final step; it packages the verified path as the
guarantee theorem. Tactics invoke the megakernel's C symbolic-execution,
bounded-execution, frame-checking, simplification, and specification-checking
axioms to prove the named guarantee. When a tactic can replay one of these
deterministic scripts, the verified theorem records that script as its
proof-step certificate.

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
`n * 4`, and `valid_range(pointer[start..end])` for half-open `int32` element
segments such as `valid_range(p[0..n])`. It also supports
`disjoint(left[start..end], right[start..end])` for half-open `int32` element
segments. The `..` form is Click C-reference syntax, not C expression syntax.
`requires` also supports Click propositions over parameters and literals.
`ensures` clauses use Click proposition syntax:

```text
result == x and not (result != x)
result == x implies result >= 0
forall (int32 k) { 0 <= k implies k >= 0 }
p[0] == old(p[0])
forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) }
```

Logical structure uses Click words: `and`, `or`, `not`, `implies`, and
`forall`. C operators such as `&&`, `||`, and `!` remain C expression syntax
and are not reused as proposition connectives. Proposition comparisons embed
small C0 integer expressions over `result`, parameters, literals, parentheses,
`+`, `-`, and post-state `p[i]` memory reads. Postconditions can use
`old(expression)` to evaluate an expression in the pre-call state, which
supports first-frame claims like `p[0] == old(p[0])`. The parser and kernel
representation accept `forall (int32 name) { ... }`. `auto` can prove simple
quantified array-segment postconditions, including unchanged-memory cases and
first frame facts outside a loop write footprint. `auto` also supports
proposition-level loop invariants, including bounded universal quantifiers over
current-state array reads.

Proof clauses currently support three tactics:

```text
by simp;
by frame;
by auto;
```

`simp` is deterministic local normalization. It simplifies proposition
connectives, constant and reflexive integer comparisons, and small arithmetic
forms such as `x + 0`. In this first version, `simp` is only accepted for
straight-line function postconditions; it does not prove effects, generate loop
verification conditions, infer frame facts, or instantiate quantified loop
invariants. `frame` is deterministic effect checking for `immutable` and
`mutable` clauses. It proves that the actual external writes stay inside the
declared frame, and rejects ordinary `ensures` postconditions. `auto` is the
broader orchestration tactic: it runs the current symbolic-execution and loop-VC
workflow, then uses the deterministic kernel reasoners to discharge the
resulting obligations. The intent is that future proof work should add named
deterministic steps first, and let `auto` become a convenience wrapper around
those steps. The first certificate path is in place: successful `auto` proofs
try to attach a replayed proof-step script when today's deterministic steps can
express the proof, including bounded concrete-loop postcondition proofs.

Function-level effect clauses are explicit and separate from postconditions:

```text
immutable by frame;
mutable p[0..n] by frame;
mutable dst[0..n], counter[0..1] by frame;
```

`immutable` proves that the function mutates no externally visible memory.
`mutable pointer[start..end]` proves that every externally visible memory cell
changed by the function falls inside the listed half-open `int32` element
segment, evaluated against the function-entry parameter values. Multiple
mutable segments form a union. Local stack bookkeeping and internal havoc
markers are not part of this external frame check. `frame` checks each effect
guarantee on every symbolic verification path. `auto` can also prove effect
clauses, and additionally proves ordinary postconditions. That sidecar path
parses C0 source, builds the requested initial memory, first tries loop
verification conditions for annotated loops, checks each postcondition or effect
clause, and packages the result as a megakernel `CFunctionSpecification`
theorem. If the loop VC path cannot prove a guarantee but leaves no invariant
obligations, `auto` can still use bounded execution for finite concrete-loop
demos.

`assert` and `invariant` clauses parse the same proposition syntax. `assert`
currently accepts only the executable fragment: comparisons, `and`, `or`, `not`,
and `implies` over current-state C0 expressions. `invariant` accepts
propositions including `forall (int32 name) { ... }`. `old(...)` inside an
invariant refers to the enclosing function's entry state.

The sidecar also has first structural proof blocks for intra-function proof
obligations:

```text
statement 2 {
    assert i == 0 by auto;
}

loop 0 {
    invariant i >= 0 by auto;
    invariant i <= 3 by auto;
    mutable p[0..3] by frame;

    step {
        mutable p[i..i + 1] by frame;
    }
}
```

`statement N` names the Nth source statement in structural order; `loop N`
names the Nth `while` loop. `assert` is a one-shot ghost check at the
structural target. `invariant` generates non-unrolling loop verification
conditions: entry checks, one-body preservation checks, and exit facts from the
invariant plus the false loop condition. Direct `mutable` and `immutable`
inside a `loop N` block are whole-loop effect clauses: they say the dynamic
execution of the loop mutates no externally visible memory outside the declared
stable footprint. Whole-loop `mutable` segments may use stable names such as
parameters, but cannot use locals modified by the loop; use an explicit
`step { ... }` block for iteration-relative footprints such as
`mutable p[i..i + 1] by frame;`. Function-level mutable clauses use
function-entry parameter values. Loop-level effect clauses should usually use
`by frame;`, though `by auto;` is still accepted for compatibility with the
broader orchestration path. Failed proof attempts report the guarantee label,
execution path, available requirements, path facts, and remaining proof
obligations.

The current loop VC path handles scalar loop locals by assigning fresh symbolic
values at the loop head. That is enough for proofs such as symbolic
`count_to_n(n)` with invariants `i >= 0` and `i <= n`, and symbolic pointer-loop
safety with `valid_range(p[0..n])`. Pointer-writing loops now produce a fresh
unknown heap state instead of implicitly preserving old memory. Written-segment
postconditions can be proved with explicit quantified invariants such as
`forall (int32 k) { 0 <= k and k < i implies p[k] == k }`. Old-memory frame
proofs across pointer-writing loops can be proved with compact segment
invariants stated directly with `old(...)`. Whole-loop `mutable` clauses now
also become reusable frame facts: if a loop declares `mutable dst[0..n]` and a
requirement proves `disjoint(dst[0..n], src[0..n])`, `auto` can use that frame
fact to prove source-memory claims such as `src[k] == old(src[k])` without a
handwritten source-frame invariant. Copy loops can prove quantified
destination-prefix facts such as `dst[k] == old(src[k])` using that idiom. The
current fixed-size pointer demos continue to use bounded execution for some
final memory facts.

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
  loop safety and `result == n` using a symbolic valid range.
- `fill_n_segment_invariant(int32 p[], int32 n)` proves a quantified
  written-segment postcondition from a quantified loop invariant.
- `fill_tail_keeps_first(int32 p[], int32 n)` proves an old-memory frame
  postcondition from an explicit loop invariant using `old(...)`.
- `fill_tail_old_prefix_segment(int32 p[], int32 n)` proves an old-memory frame
  postcondition from an explicit quantified loop invariant.
- `fill_n_mutable_segment(int32 p[], int32 n)` proves that a symbolic
  pointer-writing loop mutates only `p[0..n]`.
- `fill_n_loop_mutable_segment(int32 p[], int32 n)` proves an explicit
  `step` effect clause for each loop body step, using the per-iteration segment
  `p[i..i + 1]`.
- `loop_frame_segment_shapes` covers additional loop-level `frame` shapes:
  whole-loop shifted suffixes plus step-relative growing prefixes and
  multi-segment mutable footprints.
- `disjoint_symbolic_unwritten_read` proves a symbolic old-memory read from
  `requires disjoint(p[i..i + 1], p[j..j + 1])`.
- `count_to_three_loop_immutable()` proves a loop-level `immutable` clause for
  a scalar loop that only updates stack-local state.
- `copy_n_segment_invariant(int32 dst[], int32 src[], int32 n)` proves a
  symbolic copied segment with a quantified destination-prefix invariant plus a
  whole-loop mutable frame and a disjoint source/destination requirement; the
  source-frame guarantee uses an explicit proof-step script.
- `simp_postconditions(int32 x)` proves straight-line postconditions with
  deterministic local simplification.

The fixed-size pointer demos use 12-byte backing blocks and prove without
leftover memory-safety premises. The symbolic pointer-loop demos instead use
requirements such as `valid_range(p[0..n])` plus loop invariants. The sidecar
can also prove post-state memory guarantees such as
`ensures p[2] == 2 by auto;` and simple old-value guarantees such as
`ensures p[0] == old(p[0]) by auto;`.

## Near-Term Roadmap

1. Continue broadening loop/function frame coverage for aliasing, pointer-base
   expressions, richer segment arithmetic, and reusable frame facts.
2. Improve fact management inside `auto`, especially using requirements,
   invariants, generated frame facts, and path facts to prove postconditions
   without bounded fallback.
3. Expand proof-step coverage beyond symbolic execution, bounded execution,
   loop VCs, frame checks, simplification, and close.
4. Broaden tactic expansion into deterministic proof steps, so more successful
   `auto` proofs leave replayable certificates.
5. Grow C-native memory objects: local arrays, richer pointer ranges, and
   clearer frame conditions.
6. Add richer C integer coverage: unsigned operations, more widths, casts, and
   promotion rules.
7. Expand modular function-contract reasoning so call sites can use proven
   requirements and guarantees without inlining every function body.
8. Replace the toy C0 parser with a path toward real C parsing when the proof
   model is ready for it.
9. Split `src/megakernel.rs` into smaller modules when that helps development,
   without changing semantics.

## Verification

Run the test suite with:

```sh
cargo test
```
