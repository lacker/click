# Architecture

Click is divided into a source-language front end, proof construction and
replay, a kernel semantic core, and command-line orchestration.

## Repository map

| Path | Responsibility |
| --- | --- |
| `src/lang/c/` | Parse and represent the supported C0 source language. |
| `src/lang/click/parser.rs` | Tokenize and parse Surface Click. |
| `src/lang/click/validation/` | Resolve declarations and enforce source-level type and form rules. |
| `src/lang/click/lowering/` | Translate checked surface contracts, propositions, resources, and source locations. |
| `src/lang/click/checking/` | Evaluate contract forms and connect them to kernel structures. |
| `src/lang/click/proof/` | Construct proofs, manage proof state, replay certificates, and synthesize surface expansions. |
| `src/kernel/` | Define primitive terms, states, rules, symbolic execution, assumptions, and memory reasoning. |
| `src/cli.rs` | Shared CLI parsing, target selection, durations, and user-facing command metadata. |
| `src/bin/` | Thin entry points and command-specific reporting for verify, profile, expand, and audit. |
| `src/instrumentation.rs` | Work attribution, deadlines, budgets, and profiler events. |
| `src/persistent.rs` | Persistent structures used where proof states share prior versions. |
| `stdlib/prelude.click` | Public Click declarations loaded with user source. |
| `mdtests/`, `examples/` | End-to-end proof fixtures. |

## Data flow

The C and Click parsers retain source spans. Validation builds a
`C0VerificationSession`, which owns checked declarations and function blocks.
Lowering records the relationship between surface propositions and kernel
propositions so diagnostics and expansion can return to source language.

Proof construction operates over a replay state containing facts, symbolic C
paths, resources, and proof-site context. Smart planners may propose
transitions, but `ProofCertificate` contains only checked simple steps.
`replay_engine` applies those steps and rejects unavailable selections or
invalid transitions. Kernel APIs expose the narrow semantic operations needed
for that checking.

## Trust and boundaries

The kernel semantics and the code that translates accepted source claims into
kernel obligations are in the trusted computing base. Smart planning isn't:
its results must replay. CLI rendering and profiling don't decide validity.
Expansion is accepted only when its certificate replays and the rendered
source verifies.

OS process wrappers aren't part of the proof architecture. CLI commands and
fixture gates call the shared bounded verification engine directly. Deadlines
contain hangs; deterministic work budgets define normal proof-search bounds.

## Extension paths

When adding a public surface, change its authoritative implementation and its
reference inventory in the same slice:

- a language form normally touches the parser, syntax type, validation,
  lowering, printing, tests, and language reference;
- a tactic touches the surface enum/parser, classification, replay or planning,
  printing/expansion, tests, and tactic reference;
- a kernel rule needs a focused kernel regression and an explicit account of
  why the rule is sound;
- a CLI option belongs in shared metadata and command tests before its
  synchronized reference entry;
- a standard-library declaration belongs in `stdlib/prelude.click`, an mdtest,
  and the source-checked library reference.

See [Feature playbook](feature-playbook.md) for the review sequence and
[Testing](testing.md) for the complete gate.
