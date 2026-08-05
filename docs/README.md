# Click Book

Click is an experimental verifier for a small C subset. A `.click` sidecar
names one or more C sources, gives C functions contracts, and asks the kernel to
prove each guarantee.

This book is organized by reader need:

- **Basic Click** teaches the shape of Click: C files, sidecar specs,
  contracts, propositions, and proof scripts. Read this first if you want to
  understand simple Click code.
- **Intermediate Click** explains the concepts needed for larger verification:
  C fragments, undefined behavior, memory loadability, permissions, aliasing,
  frames, loops, predicates, pure Click functions, spec state, and example
  projects.
- **Advanced Click** is for people changing Click itself: testing, feature
  development, proof capabilities, roadmap, and kernel internals.
- **Reference** keeps the exhaustive technical pages. These pages are less
  tutorial-shaped and more precise.

The beginner chapters are intentionally a narrative spine. The reference pages
remain the source of detailed syntax and implementation truth.

## What Click Is Today

Click is a proof sidecar for a tiny C subset called C0. A `.click` file names
one or more C sources, gives C functions contracts, and asks the kernel to
prove each guarantee. The system is intentionally small but already supports:

- C0 symbolic execution over `int32`, `uint8`, pointers, memory, local arrays,
  loops with invariants, and exact struct or runtime-sized `int32`-array
  `malloc`/`free` lifetimes.
- Function contracts with `requires`, `ensures`, `immutable`, and `mutable`.
- Click propositions with `and`, `or`, `not`, `implies`, `forall`, `exists`,
  range `.all`, and range `.any`.
- Pure Click functions with `->`, `let`, `if`, range `.fold`, and calls from
  specs.
- Named Click predicates, explicit `unfold`, and a small standard prelude with
  `count` and `permutation`.
- Memory-qualified, element-typed Click array refs for pure functions and
  predicates, including `old(p)` as an entry-state array argument.
- Viewed/owned memory resources, composite resources, and exclusive allocation
  authority that must be returned or discharged by `free`.

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
which would add mdBook as a library dependency of Click. Once installed, serve
this book with:

```sh
mdbook serve
```

This builds the book, serves it at `http://localhost:3000`, and rebuilds on
changes. Use `mdbook build` only when you want static HTML output without a
local server.

Use `rg` to find examples before inventing syntax:

```sh
rg -n "unfold\\(|mutable|loadable|permutation|\\.fold|forall|exists" mdtests docs src
```

## Editing Rule Of Thumb

When adding a feature, add or update an mdtest first, then implement the parser,
lowering, kernel/prover behavior, and docs together. If a proof feature is only
documented in source comments, future agents will miss it.
