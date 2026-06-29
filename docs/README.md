# Click Book

Click is an experimental verifier for a small C subset. A `.click` sidecar
names one or more C sources, gives C functions contracts, and asks the kernel to
prove each guarantee.

This book is the linear technical introduction to the system. Read the learning
chapters in order if you want to understand the current design before changing
it:

1. [quickstart.md](quickstart.md): how to run the project and add an mdtest.
2. [c0-subset.md](c0-subset.md): the C subset and C fragments Click
   understands today.
3. [click-language.md](click-language.md): `.click` syntax and semantics.
4. [click-core.md](click-core.md): how C values elaborate into pure Click
   values such as array refs.
5. [proof-workflow.md](proof-workflow.md): tactics, proof steps, and debugging.
6. [memory-model.md](memory-model.md): pointers, ranges, aliasing, and frames.
7. [standard-library.md](standard-library.md): `stdlib/prelude.click`.
8. [examples.md](examples.md): canonical mdtests by proof pattern.
9. [limitations.md](limitations.md): current boundaries and common traps.
10. [feature-playbook.md](feature-playbook.md): how to extend Click safely.
11. [roadmap.md](roadmap.md): milestone path toward verifying a real C library.
12. [kernel.md](kernel.md): kernel implementation map for Rust changes.

[proof-landscape.md](proof-landscape.md) is the proof-capability matrix. Read it
after [roadmap.md](roadmap.md) when deciding what proof capability should come
next.

## What Click Is Today

Click is a proof sidecar for a tiny C subset called C0. A `.click` file names
one or more C sources, gives C functions contracts, and asks the kernel to
prove each guarantee. The system is intentionally small but already supports:

- C0 symbolic execution over `int32`, `uint8`, pointers, memory, local arrays,
  and loops with invariants.
- Function contracts with `requires`, `ensures`, `immutable`, and `mutable`.
- Click propositions with `and`, `or`, `not`, `implies`, `forall`, `exists`,
  range `.all`, and range `.any`.
- Pure Click functions with `->`, `let`, `if`, range `.fold`, and calls from
  specs.
- Named Click predicates, explicit `unfold`, and a small standard prelude with
  `count` and `permutation`.
- Memory-qualified, element-typed Click array refs for pure functions and
  predicates, including `old(p)` as an entry-state array argument.

Use these names consistently:

- **Kernel Click**: the explicit proof core the kernel reasons about.
- **Surface Click**: user-written `.click` syntax such as contracts,
  invariants, pure functions, predicates, `old`, quantifiers, and folds.
- **C fragments**: pieces of C0 syntax inside Surface Click. They keep C-like
  local parsing and typing, but Surface Click owns their meaning and elaborates
  them into Kernel Click.

## High-Value Commands

```sh
cargo check
cargo test
cargo test --test mdtests
```

Install the `mdbook` CLI with `cargo install mdbook`; do not use `cargo add`,
which would add mdBook as a library dependency of Click. Once installed, build
or preview this book with:

```sh
mdbook build
mdbook serve
```

Use `rg` to find examples before inventing syntax:

```sh
rg -n "unfold\\(|mutable|valid_range|permutation|\\.fold|forall|exists" mdtests docs src
```

## Editing Rule Of Thumb

When adding a feature, add or update an mdtest first, then implement the parser,
lowering, kernel/prover behavior, and docs together. If a proof feature is only
documented in source comments, future agents will miss it.
