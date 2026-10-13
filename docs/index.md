# Click reference

Click is a verifier for existing C, C++, and Rust programs. A `.click` sidecar
names source files, specifies contracts, and supplies proofs that the
implementation meets those contracts.

This is the AI reference: written for AI agents that use Click to verify code
and, in its second part, for agents that develop Click. Agents maintain it and
keep it accurate, dense, and backed by checked examples; treat an error in it
as a Click bug. The human-written guide is separate and lives in
[`guide/`](https://github.com/clicklang/click/tree/master/guide).

The rendered reference also serves `/llms.txt`, which indexes every page with
a one-line summary, and `/click-reference.md`, the whole "Using Click" part as
one file.

## Reading order

To verify a function today, read in this order:

1. [What Click proves](concepts/what-click-proves.md) and
   [what Click trusts](concepts/trust.md): the meaning of a passing result.
2. [Language coverage](reference/coverage.md): whether Click admits your
   language features at all.
3. [Your first proof](concepts/first-proof.md), then
   [Verify a function in your own project](concepts/own-project.md) for
   include paths, `-D` settings, libc calls, and `click import lock`.
4. [Contracts](concepts/contracts.md),
   [propositions](concepts/propositions.md),
   [proofs and proof scripts](concepts/proof-scripts.md), and the
   [proof workflow](concepts/proof-workflow.md).
5. When a proof fails: [proof-failure triage](concepts/proof-failure-triage.md).
6. Look up exact behavior in the [technical reference](reference/index.md):
   [tactics](reference/tactics/index.md), the
   [command line](reference/cli/index.md), the
   [standard library](reference/library/index.md),
   [supported C](reference/language/c.md), the
   [`.click` language](reference/language/index.md), and the
   [glossary](reference/glossary.md). Copy a nearby
   [example](reference/examples.md) instead of inventing syntax.

## Running Click

```console
$ click verify path/to/file.click
$ click verify --trace-proof FUNCTION path/to/file.click
$ click import lock path/to/file.click
```

`click verify` exits with status 0 when every claim verifies. From a checkout,
`cargo install --path . --bin click` installs the command. The
[command-line reference](reference/cli/index.md) documents every subcommand.

## Existing C is the boundary

Prove the existing program. Verify C, C++, and Rust as written: put
adaptations in contracts, lemmas, resources, and tactics, and don't weaken the
claim or rewrite correct code into a shape the verifier prefers. Change the
source only for a real bug, undefined behavior, or an independently desirable
change.

## Standing rules

- **Click follows GCC and Clang, not the letter of the standard.** Click
  accepts what GCC and Clang accept by default
  ([supported C](reference/language/c.md)).
- **Name the target.** Without a `target` directive, C verifies as
  `x86_64-linux-userspace` (LP64, signed plain `char`). Kernel code selects
  `target "x86_64-linux-kernel";` (unsigned plain `char`); see
  [C implementation target](reference/language/c.md#c-implementation-target).
- **A refused construct is a coverage boundary, not a reason to rewrite.**
  Check the [coverage matrix](reference/coverage.md) and the
  [limitations](reference/language/limitations.md). If the construct is
  listed as supported, the refusal is a bug: file a reproduction under
  `bugs/` in the Click repository. If it is unsupported, report the missing
  functionality instead of reshaping correct code. A semantics-preserving
  translation into supported C must be labeled as such; it is not evidence
  that Click verifies the original.
- **Triage before blaming the tool.** A failed proof does not mean the program
  is wrong or Click is broken. Check the claim, then the supported semantics,
  then replace smart search with explicit steps; after a second failure at the
  same obligation, run a proof trace. Follow
  [proof-failure triage](concepts/proof-failure-triage.md).

Click is experimental, and each supported language is an incomplete subset.
Contributors start at [Internals](internals/index.md).
