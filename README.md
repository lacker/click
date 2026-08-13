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

## Technical Documentation

Click's central adoption principle is to verify existing C as written. A proof
failure is not permission to refactor working C into a verifier-friendly shape;
for supported C semantics, the adaptation belongs in the contract, proof,
language, or verifier. See
[What Click Is](docs/basic/what-click-is.md#existing-c-comes-first) and
[AGENTS.md](AGENTS.md#existing-c-is-the-verification-boundary).

Technical documentation for agents and implementers lives in [docs/](docs/).
Start with [docs/README.md](docs/README.md), which introduces the beginner,
intermediate, advanced, and reference sections.

The docs are also an mdBook. Install the `mdbook` CLI with
`cargo install mdbook`; do not use `cargo add`, which would add mdBook as a
library dependency of Click. Once installed, serve the local HTML site with:

```sh
mdbook serve
```

This builds the book, serves it at `http://localhost:3000`, and rebuilds on
changes. Static output is written to `target/click-book/`.

High-value entry points:

- [docs/basic/what-click-is.md](docs/basic/what-click-is.md): the beginner
  starting point.
- [docs/intermediate/spec-state.md](docs/intermediate/spec-state.md): current
  spec-state design position.
- [docs/advanced/proof-failure-triage.md](docs/advanced/proof-failure-triage.md):
  distinguish proof-authoring work from Click language and tooling defects.
- [docs/advanced/testing-click.md](docs/advanced/testing-click.md): test
  commands and mdtest shape.
- [docs/advanced/verification-efficiency.md](docs/advanced/verification-efficiency.md):
  the codebase-scale complexity contract for simple verification.
- [docs/feature-playbook.md](docs/feature-playbook.md): how to extend Click.
- [docs/click-language.md](docs/click-language.md): complete `.click` syntax
  reference.
- [docs/kernel.md](docs/kernel.md): Rust kernel implementation map.

Repository work follows [AGENTS.md](AGENTS.md). In particular, verifier and
proof-tooling instability takes priority over new features and example work:
slow tactics must fail locally, smart certificates must replay, expansion must
work, and normal diagnostics must remain bounded.

## Verification

Run the full test suite with:

```sh
cargo test
```

Run only the markdown integration examples with:

```sh
cargo test --test mdtests
```
