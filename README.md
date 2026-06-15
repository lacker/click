# click

`click` is an experimental systems-code theorem prover.

The current goal is concrete: make it easy to prove useful facts about C code.
The implementation direction is megakernel-first. Instead of preserving a tiny
trusted calculus and encoding systems concepts outward from it, Click puts
systems concepts directly into the trusted kernel when that makes verification
faster, simpler, or more practical.

## Megakernel Theory

Traditional theorem provers usually optimize for a very small trusted kernel.
That is a good fit for foundational mathematics. Click is aimed at systems
engineering verification, where the priority is different: prove important
facts about real programs quickly enough and ergonomically enough that the tool
can be used on large codebases.

The tradeoff is explicit. A larger trusted kernel has more implementation
surface and therefore more bug risk. In return, it can have native concepts for
the domain: bitvectors, C values, memory, undefined behavior, symbolic
execution, and eventually C-specific proof automation. For this project, that
tradeoff is intentional.

The old list-based kernel and prelude were useful prototypes. They explored
LCF-style theorem objects, values versus computations, effects, proof scripts,
tactics, simplification, list/nat libraries, and source loading. That path is no
longer the implementation roadmap. The current crate has been cut down to the
megakernel, the C0 importer, and the first `.click` sidecar verifier.

## Architecture

The public crate currently has three modules:

- `src/megakernel.rs`: native theorem-producing operations for systems-code
  reasoning. `Theorem` remains an abstract object; callers can inspect its
  proposition but cannot construct arbitrary theorems directly.
- `src/lang/c/`: a tiny C0 syntax importer. It parses a deliberately small C
  subset and lowers it to megakernel C functions/statements/expressions.
- `src/lang/click.rs`: a first `.click` sidecar verifier slice for C0.

The megakernel currently has native data structures for:

- `Bv32Term` and `BoolTerm`
- C values, expressions, statements, functions, and function environments
- local state and memory with explicit byte-sized blocks
- expression, statement, and function outcomes
- C undefined behavior and runtime errors
- propositions, assumptions, proof obligations, path facts, and theorems

## C0 Status

C0 is not a standard language name here; it is this repo's tiny C subset used
to drive the design. It currently supports:

- `int32` and `int32*`
- integer literals and variables
- signed comparisons and equality, returning `int32` `0` or `1` like C
- signed addition and subtraction, with signed-overflow UB
- local `int32` declarations
- assignment and sequencing
- `if` / `else` with C scalar truthiness
- `while`, currently concrete/fuel-capped with invariant slots
- `return`
- address-of locals
- pointer arithmetic for `int32*`
- loads and stores
- known function calls through a small `CFunctionEnv`

The memory model has named blocks with byte sizes. Concrete in-range loads and
stores discharge memory-validity obligations directly. Out-of-range or unknown
memory accesses become proof obligations or UB depending on the execution path.

## Proof Surface

The primary proof engine today is native symbolic execution in the megakernel.
It produces theorem objects for expression evaluation, statement execution,
function execution, and function-spec satisfaction.

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
verify fill3 in "fill3.c" {
    requires valid_range(p, 12);
    ensures result == 2;

    proof {
        auto;
    }
}
```

That sidecar path parses C0 source, builds the requested initial memory, runs
native symbolic execution, checks the result clause, and packages the result as
a megakernel `CFunctionSpec` theorem.

## Current Demo

The first memory-safety demo is `fill3(int32* p)`: it writes three consecutive
`int32` cells through `p + i` in a loop and reads back the final cell. With a
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
5. Grow memory reasoning toward arrays, pointer ranges, and frame conditions.
6. Replace the toy C0 parser with a path toward real C parsing when the proof
   model is ready for it.

## Verification

Run the test suite with:

```sh
cargo test
```
