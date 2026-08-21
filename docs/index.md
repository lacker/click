# Click documentation

Click is a verifier for existing C programs. A `.click` sidecar names C source
files, specifies contracts, and supplies proofs that the implementation meets
those contracts.

These technical pages are written and maintained by AI. They aim to be
accurate, exhaustive, and mechanically checked against Click's source and
tests. They are deliberately separate from the future human-written guide,
which will have its own authorial voice and way of teaching Click. Treat a
documentation error as a Click bug and report it with the source pattern that
contradicts the page.

The documentation assumes broad programming experience but no background in
theorem proving. Start with [What Click proves](concepts/what-click-proves.md)
and [Your first proof](concepts/first-proof.md) if Click is new to you.

## Technical reference

Use the [technical reference](reference/index.md) to look up exact behavior:

- [Language](reference/language/index.md) documents Surface Click and the
  supported C0 subset.
- [Tactics](reference/tactics/index.md) inventories the proof operations and
  identifies simple, smart, and control-flow forms.
- [Command-line interface](reference/cli/index.md) documents verification,
  profiling, expansion, and auditing.
- [Standard library](reference/library/index.md) documents every public symbol
  in `stdlib/prelude.click`.
- [Glossary](reference/glossary.md) defines Click and theorem-prover terms.

## Concepts

The [concepts](concepts/index.md) explain the mental models that connect
individual reference entries: verification, proof construction, symbolic
execution, contracts, memory, resources, expansion, profiling, and auditing.

## Internals

The [internals](internals/index.md) describe the implementation for
contributors: parsing and lowering, proof objects, the kernel and trust
boundary, important representations, performance constraints, testing, and
extension workflows.

## Existing C is the boundary

Click adapts to working C; working C does not adapt to the verifier. Contracts,
proofs, libraries, tactics, lowering, and kernel support must handle supported
source patterns as written. A C change is appropriate only when it is an
independently desirable program change, fixes a real bug or undefined behavior,
or is a documented semantics-preserving translation into the supported C0
subset.

## Current status

Click is experimental and its supported language is intentionally small. The
[language limitations](reference/language/limitations.md) describe known
boundaries. The [roadmap](internals/roadmap.md) is project direction rather
than a promise that unimplemented behavior is available.
