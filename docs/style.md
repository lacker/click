# Click documentation style

This page defines project-specific rules for the AI reference. Follow the
[Google Developer Documentation Style Guide](https://developers.google.com/style/)
when this page does not state a Click-specific rule.

## Audience and purpose

Write for a reader with broad programming experience and no theorem-prover
experience. Reference pages optimize for accuracy, coverage, consistent
structure, and fast lookup. Concept pages explain one mental model. Internal
pages explain the implementation and the invariants a contributor must
preserve.

This is the AI reference, written for AI readers and maintained by agents. The
human-written guide in the repository's `guide/` directory is the maintainer's;
agents do not edit it or blend its prose into this corpus.

Each page opens with a prose paragraph whose first sentence says what the page
covers. That sentence is the page's description in the generated `llms.txt`, so
it can't be a list or example lead-in ending in a colon.

## Source fidelity

The implementation and its passing tests are authoritative. Use the public
surface inventory to ensure coverage, but verify semantics against the parser,
validation, lowering, prover, kernel, CLI implementation, standard library,
and focused regressions.

Do not change C to make documentation easier to write. If supported existing C
cannot prove a true claim, document or fix the Click gap. If a smart tactic
times out, produces an expansion that doesn't verify, or requires unnatural
proof bookkeeping, follow the tooling-stability policy in `AGENTS.md`.

Normative examples must be backed by an mdtest, an example project, or a checked
source include. Immediately precede each normative `click` or `c` fence with a
`verified-example` comment naming that fixture. The standard-library reference
is the one exception: its exact declaration blocks are synchronized directly
with the `library/` modules, and every symbol has a checked use in the library
mdtest. The tactic fixture catalog maps every selectable tactic form to the
source text that exercises it. Use a negative fixture for a normative failure
diagnostic.

## Voice and structure

- Use sentence case for titles, headings, and navigation.
- Address the reader as "you" only when describing an action the reader takes.
- Prefer active voice and present tense.
- State the rule before background or exceptions.
- Use one H1 per page and do not skip heading levels.
- Keep a page focused on one lookup family, mental model, or subsystem.
- Use descriptive link text instead of "here" or a bare URL.
- Use relative `.md` links within `docs/`. Use an absolute repository URL when
  a source link intentionally leaves the published documentation tree.
- Put filenames, commands, syntax, symbols, and code terms in code font.
- Tag every fenced code block with its language or with `text`.
- Put copyable commands in `console` fences. Put noncopyable command syntax in
  `text` fences, and describe it as a synopsis or usage form.
- Introduce command output before its fence and label abbreviated output with
  an ellipsis or an explicit note.
- Use uppercase descriptive placeholders such as `PATH` and `CLAIM` in command
  syntax; explain placeholders in appearance order.
- Use notes sparingly. Begin a freestanding note with `> **Note:**` and keep
  warnings focused on an action and its consequence.
- Label unsupported, experimental, compatibility-only, deprecated, and
  internal behavior explicitly. Parser acceptance alone is not a stability
  promise.

## Proof example conventions

For a function whose proof needs only the implicit tail, which runs the
remaining C and closes every open goal, omit the proof clause. A script
needs no final closer. Where work follows at function exit, step there with
`step_until(function.exit);`, and where paths need different work, write
`branch` at the C `if`, or a proof `if` before the C, with each arm stepping
to exit. For a one-tactic
proof, use `by T(args);`, such as `by close();`, or `by close();` for a
claim with no C left, such as a `have` or a pure theorem. Braces
are optional around that single tactic. Use `by { ... }` for a sequence of
tactics. Call-style tactics always take parentheses, including `close()`.
Write `close()`, `close() using`, and `step_until`. The parser refuses
`known`, `solve`, `assumption`, `auto`, `arithmetic`, `execute`, and
`execute_until`. Structural forms such as `if`, `match`, and `have` retain their
own grammar. Write `then` after a proof `if`'s `ensuring` interface. In a
`branch`, write `true => { ... }` and `false => { ... }` inside the arm block.
Call modifiers follow the
parenthesized head, as in `step() by { ... }`.

End call statements with `;`, including calls with a `using { ... };` list.
Do not add a trailing semicolon to proof-control blocks such as `by { ... }`,
`if`, `all`, or `loop`. The parser still accepts redundant semicolons.
Generated premise lists put each premise on its own line. Wrap long premises
and certificate entries near 100 columns with a further four-space indentation;
keep quoted literals and individual tokens intact.

Use semantic proof marks for states a handwritten proof has already reached.
Use numeric statement selectors when the example needs to target a source
coordinate or explain generated output. A mark names a recorded state;
it is not an execution target. See
[Proof workflow](concepts/proof-workflow.md#frontier-facts-and-loop-proofs) for the checked example.

## Canonical terms

- **Surface Click** is the user-written `.click` language.
- A **target language** is the language of the program being verified; the
  target languages are supported C, C++, and Rust. Surface Click is the
  **specification language**, in which contracts, models, and proofs are
  written. Rust is also Click's implementation language. Do not write
  *program language* or *proof language*.
- A **function head** (of a verified function, an `extern`, or a `contract`)
  restates a target-language declaration. Write it as the source writes the
  declaration: `long long` where the source says `long long`, `int` where it
  says `int`. Click checks the head's exact types; the written form is this
  convention.
- **Kernel Click** is the explicit proof core. It has no textual user syntax.
- **Lowering** turns a Surface term into a kernel term, **raising** turns a
  kernel term into a Surface term, and **printing** turns a Surface term into
  text. What an author or a target-language source wrote is its **source
  text**. A kernel term **raises** when raising gives a Surface term that
  lowers back to it. Do not write *spell*, *spelling*, or *spellable*: say
  raise, print, source text, form, or name, whichever is meant.
- A **C fragment** is C syntax embedded in Surface Click and elaborated into
  Kernel Click meaning.
- A **sidecar** is a `.click` file that specifies one or more target-language
  sources.
- A **proof unit** is one independently selectable function claim or theorem
  proof together with the dependencies needed to check it.
- **Proof state** is the user-facing model of the current goals, facts,
  resources, and execution frontier.
- A **proof object** is the kernel-owned persistent representation of semantic
  proof state, open branches, and focus. **Proof lineage** is the separate
  language-layer record of surface-expressible checked operations. Use both
  terms in Internals, not as artifacts that proof authors manipulate.
- A **certificate** is a surface-expressible explicit proof used as
  independently checkable output, especially by expansion. It is not a
  required intermediate artifact of ordinary verification.
- A **certificate step** is one explicit node in that internal serialization.
  It may be a simple operation or a nested control structure, but never a smart
  tactic; a **simple tactic** is a Surface Click command that requests one
  deterministic checked operation.
- A **kernel derivation** is standalone trusted typed evidence produced by a
  kernel rule. A checked proof-object successor can also embody transition
  authority without retaining a separate derivation value. Don't call a
  certificate, proof lineage, or an evolving proof object a kernel
  derivation.
- **Expansion** replaces smart proof source with an extracted explicit proof
  and verifies the complete rewritten source through ordinary verification.
- Use **round-trip validation** for checking generated proof text through the
  ordinary verifier. Don't present it as a separate phase of ordinary
  verification.
- A **point** is a node in the code's region tree (`function.entry`,
  `region(N).exit`, a statement's entry or exit, a label, a `mark` name). It
  is only an identity and holds no data. A **location** is a position in the C
  source text; use it only when talking about the source itself, as in
  diagnostics. An **execution frontier** combines the current point with its
  symbolic state and pending continuations.
  Use *frontier* only as its short form.
- A **proof branch** is one independently evolving open proof. A **C branch**
  is source control flow with syntactic arms, and an **execution path** is one
  symbolic route through C. Do not use these terms interchangeably.
- On a proof path, `at(x, e)` means `e` when the path was at point `x`; a
  proof path reaches each point at most once. A **version point** is the point
  a memory read is lowered to. *Program point* is a synonym for point, for
  where *point* alone reads too vaguely. Neither word means the memory or
  state at a place: "the memory at a point" is not an object a proof refers
  to; what is known there is facts about reads there. Don't use *state*,
  *memory state* or *visit* as user-facing concepts.
- `old`, `at`, `exact` and `defined` are the **special forms**: built-in
  syntax that changes how its argument is read or lowered. `old`, `at` and
  `exact` are **point selectors**; `defined` is a proposition. Call them by
  these names, not constructs, wrappers, operators or built-ins, and don't
  extend either name to other built-in syntax such as `result` or `count`.
- A **proposition** is a neutral logical statement. A **claim** is selected for
  verification, a **goal** is open in a proof, and an **obligation** is
  generated by a semantic rule.
- A **fact** is an established proposition. An **assumption** is accepted as an
  input in the current context; a **premise** is consumed by one rule.
- A **load term** is a read at its version point. Its **load variable** is the
  canonical form shared across derivation steps that don't write the cell.
  Crossing a write requires explicit **fact transport**, not a state bridge.
- An **execution fact** is produced while symbolically executing a path. A
  **memory-effect fact** is the retained subset that carries mutation, free, or
  transport evidence. Use the qualified term; bare *effect fact* is easily
  confused with a contract effect.
- A **memory derivation DAG** records how kernel memory values were produced. Don't
  shorten this to *memory DAG* in explanatory prose.

Use the [glossary](reference/glossary.md) for the full vocabulary.

## Reference entry templates

### Language construct

State syntax, allowed context, validation and type rules, visible semantics,
proof or resource effects, a verified example, unsupported nearby forms, and
related entries.

### Tactic

State syntax and variants, class, accepted proof state, consumed and produced
state, checking behavior, smart-search failure behavior when applicable,
expansion and profiling behavior, a verified example, and retired forms.

### Command

State synopsis, purpose, targets, arguments, every option and default, output,
exit behavior, examples, relevant environment variables, and related
commands. Keep exact synopsis text synchronized with command metadata.

### Library symbol

State the exact source declaration, meaning, parameters, requirements and
guarantees, unfolding or resource behavior, a verified use, and related
symbols. Never maintain an unchecked second copy of a declaration.
