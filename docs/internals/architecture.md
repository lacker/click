# Architecture

Click is divided into a source-language front end, proof construction, a
kernel semantic core, and command-line orchestration.

## Repository map

| Path | Responsibility |
| --- | --- |
| `src/lang/c/` | Parse and represent the supported C0 source language. |
| `src/lang/click/parser.rs` | Tokenize and parse Surface Click. |
| `src/lang/click/validation/` | Resolve declarations and enforce source-level type and form rules. |
| `src/lang/click/lowering/` | Translate checked surface contracts, propositions, resources, and source locations. |
| `src/lang/click/checking/` | Evaluate contract forms and connect them to kernel structures. |
| `src/lang/click/proof/` | Interpret tactics, orchestrate checked proof operations, run smart search, and synthesize surface expansions. |
| `src/kernel/` | Define primitive terms, states, rules, symbolic execution, assumptions, memory reasoning, and the persistent checked proof object. |
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

The kernel's persistent `ProofObject` owns typed obligations, facts, symbolic
C execution, resources, focus, and checked successor authority. A
language-layer `Proof` pairs that opaque handle with checking context and
Surface provenance. Explicit tactics request named simple or structural
operations. Smart planners try the same operations transactionally on
persistent `Proof` descendants; they can't construct semantic successors
directly. Kernel APIs expose the primitive logical, execution, memory, and
resource operations needed for that checking.

The checked drivers are the single verification engine: a source or generated
proof tree is checked by advancing a persistent `Proof`, and a shape no driver
accepts is a terminal error, never a reason to run a second engine.
`ExecutionProofState` is the typed execution snapshot inside a `Proof`: the
frontier, path state, and surface record it owns are the execution model, and
the only cursor it carries is where a source tactic's expansion is being
captured.

`ProofCertificate` is the current structured form for a surface-expressible
explicit proof. In the intended architecture it is serialization: expansion
extracts attributed operations from checked `Proof` provenance only when proof
text or an inspection result is requested.

## Trust and boundaries

The kernel semantics and the code that translates accepted source claims into
kernel obligations are in the trusted computing base. Smart planning isn't:
it can advance proof state only through checked operations. CLI rendering and
profiling don't decide validity. Expansion is accepted only after the complete
rendered source verifies through the ordinary entry point.

The ordinary `Proof` transition boundary and rewritten-source verification
are the durable invariants; no separate certificate validation sits in front of
that check.

OS process wrappers aren't part of the proof architecture. CLI commands and
fixture gates call the shared bounded verification engine directly. Deadlines
contain hangs; deterministic work budgets define normal proof-search bounds.

## Extension paths

When adding a public surface, change its authoritative implementation and its
reference inventory in the same slice:

- a language form normally touches the parser, syntax type, validation,
  lowering, printing, tests, and language reference;
- a tactic touches the surface enum/parser, classification, its checked `Proof`
  operation or smart planning, printing/expansion, tests, and tactic reference;
- a kernel rule needs a focused kernel regression and an explicit account of
  why the rule is sound;
- a CLI option belongs in shared metadata and command tests before its
  synchronized reference entry;
- a standard-library declaration belongs in `stdlib/prelude.click`, an mdtest,
  and the source-checked library reference.

See [Feature playbook](feature-playbook.md) for the review sequence and
[Testing](testing.md) for the complete gate.
