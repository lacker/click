# Click documentation style

This page defines project-specific rules for the AI-written technical
documentation. Follow the
[Google Developer Documentation Style Guide](https://developers.google.com/style/)
when this page does not state a Click-specific rule.

## Audience and purpose

Write for a reader with broad programming experience and no theorem-prover
experience. Reference pages optimize for accuracy, coverage, consistent
structure, and fast lookup. Concept pages explain one mental model. Internal
pages explain the implementation and the invariants a contributor must
preserve.

The technical reference, Concepts, and Internals are written and maintained by
AI. A future human-written guide is a separate work. Do not blend its prose into
this corpus or rewrite it into the technical-reference voice without explicit
authorization.

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
with `stdlib/prelude.click`, and every symbol has a checked use in the library
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

## Canonical terms

- **Surface Click** is the user-written `.click` language.
- **Kernel Click** is the explicit proof core. It has no textual user syntax.
- A **C fragment** is C0 syntax embedded in Surface Click and elaborated into
  Kernel Click meaning.
- A **sidecar** is a `.click` file that specifies one or more C sources.
- A **proof unit** is one independently selectable function claim or theorem
  proof together with the dependencies needed to check it.
- **Proof state** is the user-facing model of the current goals, facts,
  resources, and execution frontier.
- A **proof object** is the internal persistent representation of proof state
  and checked transition history. Use the term in Internals, not as an artifact
  that proof authors manipulate.
- A **certificate** is a surface-expressible explicit proof used as
  independently checkable output, especially by expansion. It is not a
  required intermediate artifact of ordinary verification.
- A **certificate step** is one simple operation in that internal
  serialization; a **simple tactic** is the Surface Click command that requests
  the corresponding checked transition.
- A **kernel derivation** is trusted typed evidence for a proposition or state
  transition. Don't call a certificate or an evolving proof object a kernel
  derivation.
- **Expansion** replaces smart proof source with an extracted explicit proof
  and verifies the complete rewritten source through ordinary verification.
- Use **replay** only for checking previously produced proof text again or for
  the current compatibility implementation. Don't present it as a required
  phase of ordinary verification.
- A **program point** is a location in C. An **execution frontier** combines
  one current program point with its symbolic state and pending continuations.
  Use *frontier* only as its short form.
- A **proposition** is a neutral logical statement. A **claim** is selected for
  verification, a **goal** is open in a proof, and an **obligation** is
  generated by a semantic rule.
- A **fact** is an established proposition. An **assumption** is accepted as an
  input in the current context; a **premise** is consumed by one rule.
- A **load term** reads one memory snapshot. Its **load variable** is the
  canonical form shared across derivation steps that don't write the cell.
  Crossing a write requires explicit **fact transport**, not a snapshot bridge.
- An **execution fact** is produced while symbolically executing a path. Use
  this term instead of *effect fact*, which is easily confused with contract
  effects.
- A **memory derivation DAG** records how memory snapshots were produced. Don't
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
expansion and profiling behavior, a verified example, and retired spellings.

### Command

State synopsis, purpose, targets, arguments, every option and default, output,
exit behavior, examples, relevant environment variables, and related
commands. Keep exact synopsis text synchronized with command metadata.

### Library symbol

State the exact source declaration, meaning, parameters, requirements and
guarantees, unfolding or resource behavior, a verified use, and related
symbols. Never maintain an unchecked second copy of a declaration.
