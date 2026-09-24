# Architecture

Click is divided into one Surface Click proof language, a family of supported
program languages, a kernel semantic core, and command-line orchestration.
Both the proof language and each program language have frontend stages such as
parsing, validation, and lowering; *frontend* names a stage, not either
language's role.

## Repository map

| Path | Responsibility |
| --- | --- |
| `src/languages.rs`, `src/languages/c.rs`, `src/languages/c/` | Parse, represent, and lower the currently supported C0 program language. Future program languages get sibling modules here. |
| `src/surface.rs` | Define Surface Click forms and connect its checking, lowering, proof, and presentation modules. |
| `src/surface/parser.rs` | Tokenize and parse Surface Click. |
| `src/surface/validation/` | Resolve declarations and enforce source-level type and form rules. |
| `src/surface/lowering/` | Translate checked surface contracts, propositions, resources, and source locations. |
| `src/surface/checking/` | Evaluate contract forms and connect them to kernel structures. |
| `src/surface/proof/` | Interpret tactics, orchestrate checked proof operations, run smart search, and synthesize surface expansions. |
| `src/source.rs` | Share source-file positions between Surface Click and program-language frontends. |
| `src/kernel/` | Define primitive terms, states, rules, symbolic execution, assumptions, memory reasoning, and the persistent checked proof object. |
| `src/cli.rs` | Shared CLI parsing, target selection, durations, and user-facing command metadata. |
| `src/bin/` | Thin entry points and command-specific reporting for verify, profile, expand, and audit. |
| `src/instrumentation.rs` | Work attribution, deadlines, budgets, and profiler events. |
| `src/persistent.rs` | Persistent structures used where proof states share prior versions. |
| `stdlib/prelude.click` | Public Click declarations loaded with user source. |
| `mdtests/`, `examples/` | End-to-end proof fixtures. |

## Data flow

The C program-language and Surface Click proof-language parsers retain source
spans. Validation builds a
`C0VerificationSession`, which owns checked declarations and function blocks.
Lowering records the relationship between surface propositions and kernel
propositions so diagnostics and expansion can return to source language.
Those records are presentation hints, not evidence that a fact is available.
Loop-head lowering returns one selected proposition per declared invariant,
including duplicates, separately from the new-fact delta. A preservation
proof records generated iteration-entry spellings against those selected
propositions in its local scope; an unqualified source spelling continues to
lower against the current C state. Certificate generation checks a candidate
spelling at its output location and validates the selected kernel premise,
never whichever available fact happens to share that spelling.

The kernel's persistent `ProofObject` owns typed obligations, facts, symbolic
C execution, resources, focus, and checked successor authority. A
Surface-layer `Proof` pairs that opaque handle with checking context and
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

### Contracts and callbacks

One body-independent contract interface carries a function's typed
parameters and result, proof binders, pure requirements and guarantees,
normalized resource clauses with their access, transfer role, and snapshot,
composite definitions, and predicate unfoldings. Verified functions, external
assumptions, named callback contracts, and execution theorems all apply
through it; their evidence stays distinct (a callback fact is tied to an exact
pointer value, an external assumption is never a verified body).

Each application prepares one resource transition: borrowed and consumed
inputs, the caller residual, the callee's context, the memory-effect
projection, and the post outputs. It has two purposes. A call site lends, so
the views it passes become loans and recovery returns them. A function
boundary, the verified-body executors, the contract entry-state builder, and
the outcome-through-contract applier, consumes the declared requirements
definitionally; its input-view loan roots come from the proof's entry
construction, so nothing is lent twice. The two agree on what the callee
receives. The callee's pure preconditions and its returned borrows are read
against the transferred clause set opened through its definitions, the way the
callee's own entry reads it.

The memory-effect projection of that transition is the only write footprint:
modular call havoc, refinement containment, certification's effect claims,
storage-write checks, and every loop frame (inherited at function entry or
declared at loop entry) derive from it. A frame check across a call or loop
havoc opens an owned composite one level, the boundary a composite lend and
`project` use, and never reads inside a folded body.

Instance binders reach one kernel map whether a proof writes a call map or a
named contract's proof arguments; an execution theorem's `as` map only renames
spellings before binding through one of those. The loan ledger, its laws, and
the call boundary's lending and recovery are in
[stable views](stable-views.md).

## Selected control-flow and C++ cleanup model

The launch control-flow slice has one checked execution-frontier model for
forward C edges and C++ cleanup edges. A frontier carries its path state and
obligations to the next source operation; a transfer does not execute skipped
statements. C forward `goto` keeps its target and source attribution, while the
C++ importer supplies checked destructor operations on normal returns and
exceptional unwinding edges. The language frontends decide which edges are
legal; the kernel does not infer cleanup or loan recovery from lexical scope
alone.

The selected C++ exception profile is deliberately closed: C++20 on the pinned
Clang/LLVM 19.1.7 `x86_64-unknown-linux-gnu` profile, exceptions enabled,
RTTI disabled, one `int32` exceptional payload, a matching `catch (int)`, and
non-throwing constructors and destructors. `throws int32` is part of the
checked Click signature. Normal `ensures` and `exceptional ensures` are
separate claim families; a missing exceptional declaration is non-throwing,
not an unconstrained promise. The locked exporter artifact records the
compiler profile and semantic input, so an exporter change cannot silently
broaden a normal-only import.

The C++ exporter uses Clang's typed AST and checked source CFG to identify the
throw, handler, payload, and constructed objects. It emits destructor calls as
ordinary checked kernel steps, in reverse construction order, and retains the
constructed prefix when a later declaration follows a potentially throwing
call. Function-scope destructor chains also run before an escaping call or
explicit throw crosses the function boundary, including when a potentially
throwing call initializes a local. ABI landing pads and runtime exception
behavior are trust-boundary inputs, not proof evidence. The supported slice
permits at most two destructible objects in the selected cleanup scope;
throwing constructors or destructors, rethrow and inherited handlers,
`setjmp`/`longjmp`, and general backward or irreducible edges remain outside
it.

The [resource tracker](resource-tracker.md) is the single kernel authority for
whether a mutable resource is the same at two proof points. Cleanup proofs use
that answer to frame destructor stores and to distinguish a real mutation from
an unshown fact; it does not grant ownership or recover a resource on its own.
The semantic regressions are `mdtests/cpp_two_guard_unwind.md`,
`mdtests/cpp_guard_unwind_before_second.md`, and
`scalar_int32_profile_emits_function_scope_cleanup_edges_for_escaping_throws`
in `tests/cpp_import.rs`. The deterministic
scaling regression
`exceptional_cleanup_edges_scale_near_linearly_with_unrelated_context` in
`src/surface/tests/scaling_tests.rs` covers cleanup-edge counts 2, 4, 8, and
16 while unrelated functions and facts grow; it checks both total work and
the named call/edge operation rather than wall time.

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

- a Surface Click form normally touches the parser, syntax type, validation,
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
