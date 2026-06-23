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

Technical documentation for agents and implementers lives in [docs/](docs/).
Start with [docs/README.md](docs/README.md), which gives the recommended reading
order for a fresh agent.

High-value entry points:

- [docs/quickstart.md](docs/quickstart.md): run the project and add mdtests.
- [docs/click-language.md](docs/click-language.md): `.click` syntax.
- [docs/c0-subset.md](docs/c0-subset.md): supported C0 syntax.
- [docs/proof-workflow.md](docs/proof-workflow.md): tactics and proof scripts.
- [docs/memory-model.md](docs/memory-model.md): pointers, ranges, aliasing, and
  frames.
- [docs/standard-library.md](docs/standard-library.md): `stdlib/prelude.click`.
- [docs/roadmap.md](docs/roadmap.md): milestone path toward real-library
  verification.
- [docs/kernel.md](docs/kernel.md): Rust kernel implementation map.
- [docs/examples.md](docs/examples.md): canonical mdtests by proof pattern.
- [docs/limitations.md](docs/limitations.md): current boundaries.
- [docs/feature-playbook.md](docs/feature-playbook.md): how to extend Click.

The proof-capability matrix remains in
[docs/proof-landscape.md](docs/proof-landscape.md).

## Verification

Run the full test suite with:

```sh
cargo test
```

Run only the markdown integration examples with:

```sh
cargo test --test mdtests
```
