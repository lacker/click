# Rebuild the technical documentation as an exhaustive AI-written reference

## Violated invariant

Click's technical documentation must let a reader with broad programming
experience, but no theorem-prover experience, discover every supported public
surface and understand it without reading the implementation. Each factual
claim, syntax form, command, tactic, and standard-library entry must agree with
the source and remain current as the source changes.

The technical reference is intentionally AI-written and AI-maintained. Its
editorial goal is precise, exhaustive, consistently structured documentation,
not an imitation of an individual human author's voice. A future human-written
guide will be a separate document with a separate identity. The published
documentation must disclose this boundary clearly and must not silently blend
the two bodies of work.

The current documentation violates this invariant in several concrete ways:

- `docs/standard-library.md` manually duplicates `stdlib/prelude.click` and
  already omits the public `allocation` resource and the
  `int32_move_one_from_right_to_left_preserves_sum` and
  `int32_le_and_neq_implies_lt` theorems.
- `docs/click-language.md` is a useful 1,000-line foundation, but it is not a
  machine-audited inventory of all keywords, declarations, types, expressions,
  operators, precedence rules, propositions, contracts, resources, effects,
  proof forms, and C0 fragments.
- `docs/proof-tactics.md` is a strong hand-maintained inventory, but nothing
  ensures that every parsed tactic and every smart, simple, or control-flow
  variant appears there with the correct classification.
- CLI material is split between testing and performance chapters. There is no
  canonical reference page for each of `click verify`, `click profile`,
  `click expand`, and `click audit`, and no check keeps documented options,
  defaults, accepted targets, or environment variables synchronized with the
  command implementations.
- There is no glossary for readers who know programming but do not yet know
  proof terminology.
- Concepts, user reference, contributor procedures, design notes, and
  implementation internals are mixed under the current Basic, Intermediate,
  Advanced, and Reference book structure.
- `docs/advanced/proof-object-api.md` is a large design and progress log rather
  than a concise description of the current architecture, and it is not listed
  in `docs/SUMMARY.md`.
- The gate in `scripts/check.sh` does not build the mdBook, validate its local
  links and anchors, lint Markdown structure, or check reference coverage.
  Code blocks in `docs/` are not exercised by the `mdtests/` harness.
- Most existing titles and navigation labels use title case rather than the
  sentence case required by the Google Developer Documentation Style Guide.
- The site calls itself a book even though the desired result is a searchable
  technical-documentation site organized by reader need.

This is a documentation and documentation-tooling issue. It does not authorize
changing existing C to make an example easier to explain or prove. Examples
must preserve the existing-source verification boundary in `AGENTS.md`.

## Editorial and authorship contract

Use the Google Developer Documentation Style Guide:

<https://developers.google.com/style/>

Add a short Click-specific documentation style page. Project-specific guidance
comes first where Click needs canonical theorem-prover terminology or a
deliberate exception; otherwise follow Google's guide. At minimum, the local
page must define:

- the audience and prerequisites for the technical reference;
- canonical spellings and distinctions for Click-specific terms;
- sentence-case headings and navigation;
- reference-entry templates for language forms, tactics, commands, and library
  symbols;
- conventions for code, placeholders, commands, output, links, notes, and
  unsupported or experimental behavior;
- the source-of-truth and test expectation for factual claims and examples;
- the boundary between AI-written technical reference and the future
  human-written guide.

Put a candid disclosure on the technical-documentation landing page. The final
wording can be edited, but it must communicate substantially the following:

> These technical reference pages are written and maintained by AI. They aim
> to be accurate, exhaustive, and mechanically checked against Click's source
> and tests. They are deliberately separate from the human-written guide,
> which has its own authorial voice and way of teaching Click.

Do not repeat a distracting banner on every page. The landing page, site
navigation, and contributor/style guidance must make the provenance boundary
discoverable. Do not call the technical reference human-written, and do not
rewrite a future human document into the reference voice without explicit
authorization.

## Storage format and renderer

Keep authored documentation in conservative Markdown under `docs/` and keep
mdBook as the renderer for this work. Treat mdBook as replaceable presentation,
not as the information architecture. Do not combine this content pass with a
move to MkDocs, Docusaurus, MDX, or a custom website framework.

Use relative `.md` links, one sentence-case H1 per page, language-tagged fenced
code blocks, stable subject-based filenames, and minimal inline HTML. Avoid
renderer-specific components. Generated fragments or includes are appropriate
only where they keep exact declarations, help text, or tested examples tied to
their source.

Rename the rendered site from "The Click Book" to "Click documentation" or an
equivalent technical-documentation title. The static mdBook output should be
ready to publish on an ordinary static host, but selecting a host and publishing
the site are separate operations unless explicitly added to this issue.

## Information architecture

Organize pages by the question the reader is asking:

```text
Click documentation
├── Technical reference
│   ├── Language
│   ├── Tactics
│   ├── Command-line interface
│   ├── Standard library
│   └── Glossary
├── Concepts
└── Internals
```

Language, tactics, the CLI, the library, and the glossary are lookup reference.
Concepts explain cross-cutting mental models. Internals explain the
implementation and trusted architecture. These areas can share the
AI-maintained technical-documentation ownership boundary without pretending
that every conceptual page is itself reference material.

Use a directory shape along these lines, adjusting individual page boundaries
after the inventory:

```text
docs/
├── index.md
├── reference/
│   ├── index.md
│   ├── language/
│   ├── tactics/
│   ├── cli/
│   ├── library/
│   └── glossary.md
├── concepts/
└── internals/
```

Reserve a separate top-level identity for the future human-written guide. Do
not invent its content, title, directory layout, or voice in this work. It is
enough for the technical landing page to explain that the guide is separate
and to link it once it exists.

Audit every existing page before moving or retiring it. Preserve accurate and
useful material, but do not preserve the current chapter structure merely to
avoid editing it. Redirect old published paths if stable public URLs exist by
the time a page moves. Keep project status and roadmap material distinct from
normative language reference.

## Source-backed coverage inventory

Create one machine-readable inventory, such as
`docs/reference/inventory.toml`, mapping stable public-surface identifiers to
the Markdown page and anchor that documents them. The precise file format is
less important than a bidirectional test:

1. Every supported public item discovered from the implementation or canonical
   public registry has exactly one reference entry.
2. Every inventory entry points to an existing page and anchor and still names
   a supported, intentionally documented item.

Cover at least:

- all user-visible Click keywords and reserved words;
- every top-level declaration and contract clause;
- types, literals, expressions, operators, precedence and associativity;
- propositions, quantifiers, ranges, folds, snapshots, C fragments, resources,
  effects, proof blocks, loop and branch forms, and supported C0 constructs;
- implicit forms and sugar, including omitted proofs and `by auto`;
- all simple, smart, and control-flow tactics, including selectable variants
  and retired spellings that still produce migration diagnostics;
- CLI commands, options, accepted targets, location syntax, defaults,
  durations, output modes, exit behavior, and public environment variables;
- every public declaration in `stdlib/prelude.click`;
- every term intentionally exposed in the glossary.

If the parser or CLI has no suitable canonical registry to compare against,
introduce the narrowest shared metadata needed for documentation and help to
agree. Do not create a second parser, recursively invoke Click commands, or
scrape stderr in the gate. The implementation remains authoritative.

## Language reference

Split `docs/click-language.md`, `docs/c0-subset.md`, and relevant material from
the beginner and intermediate chapters into focused, cross-linked pages. The
language reference must cover every accepted user-visible construct, not only
the constructs used by current examples.

Each construct entry must state, as applicable:

- canonical syntax and metavariables;
- where the form is allowed;
- static type and validation rules;
- elaboration or lowering semantics visible to the user;
- proof obligations, resource effects, or snapshot behavior;
- one minimal verified example;
- important invalid or unsupported nearby forms;
- related constructs and concepts.

Include a grammar-level overview and explicit operator precedence and
associativity. Clearly distinguish Surface Click, Kernel Click, and C fragments.
Do not imply that Kernel Click has a textual user syntax. Keep the supported C0
subset normative and separate from general C behavior. Document unsupported,
experimental, compatibility-only, and deprecated forms explicitly rather than
leaving readers to infer them from parse errors.

## Tactic reference

Rebuild `docs/proof-tactics.md` as an exhaustive reference derived from the
tactic inventory. Organize the entry points so readers can browse simple,
smart, and control-flow tactics while still finding a tactic directly by its
surface spelling.

Each tactic entry must state:

- canonical syntax and variants;
- simple, smart, control-flow, structural, or context-dependent
  classification;
- the goal and proof state in which it is valid;
- exactly what state, facts, resources, frontier, or goals it consumes and
  produces;
- deterministic replay and certificate behavior;
- search boundaries and expected failure behavior for smart tactics;
- expansion and profiling behavior;
- a minimal verified success and, where useful, a focused failure;
- replacement guidance for retired spellings.

Keep conceptual guidance about choosing tactics out of the lookup entry except
for brief usage notes. Put the smart/simple mental model, proof workflow, and
failure triage in Concepts and link to them.

## Command-line interface reference

Create an overview and one canonical reference page for each public subcommand:

- `click verify`
- `click profile`
- `click expand`
- `click audit`

Each command page must cover its synopsis, accepted targets, selection rules,
arguments, every option, defaults and limits, output, exit behavior, examples,
interaction with other commands, and relevant environment variables. Separate
copyable commands from illustrative usage syntax according to the Google style
guide.

Generate or test exact synopses and option tables against the same definitions
used by `--help`; human-authored explanations should surround this exact
material. Document `scripts/check.sh`, mdtest selection, and contributor-only
A/B environment flags in an appropriately labeled contributor/tooling area
rather than presenting them all as ordinary end-user CLI.

Move the mental models for verification, profiling, expansion, and auditing to
Concepts. Command pages define what a command does; concept pages explain why
and when the workflow exists.

## Standard-library reference

Document every public Click symbol from `stdlib/prelude.click`. Group pages by
useful families, but give each symbol a stable linkable entry containing:

- its exact declaration from the authoritative source;
- a concise semantic description;
- parameter and result meaning;
- requirements, guarantees, unfolding behavior, or resource meaning;
- one minimal verified use;
- related symbols and relevant conceptual background.

Do not manually copy exact declarations without a synchronization check. Use a
source include, generated fragment, or structural comparison that fails when
the source declaration changes. The coverage regression must immediately catch
the three currently omitted public symbols.

Clarify that this library is the public Click standard library, not the Rust
crate's internal `pub` API. Internals can link to selected Rust types and
modules; exhaustive rustdoc generation is a separate concern unless it becomes
a supported extension API.

## Glossary

Write a glossary for a programmer who has no theorem-prover background. Keep
definitions short, link them to fuller concept and reference pages, and state
important contrasts. Include at least:

- assumption, premise, fact, proposition, theorem, goal, proof, proof state;
- tactic, simple tactic, smart tactic, control-flow tactic;
- proof object, certificate, replay, kernel, trusted computing base,
  soundness, completeness, and bounded search;
- contract, precondition, postcondition, invariant, induction, quantifier,
  binder, witness, and instantiation;
- symbolic execution, execution path, frontier, branch, and join;
- definedness, undefined behavior, C0, C fragment, Surface Click, Kernel Click,
  elaboration, and lowering;
- resource, ownership, view, permission, loadability, alias, frame, effect,
  snapshot, `old`, `at`, and proof mark;
- sidecar, proof unit, expansion, profiling, audit, and mdtest.

Use one canonical term consistently throughout the corpus. Add Click-specific
terminology decisions to the local style page; do not rely on the glossary to
paper over inconsistent prose.

## Concepts

Create focused explanations of the mental models that cross reference entries:

- what Click proves and the existing-C verification boundary;
- the verification pipeline from parsing through lowering, proof construction,
  kernel checking, and diagnostics;
- goals, facts, proof state, proof scripts, proof objects, and replay;
- simple tactics, smart tactics, bounded incompleteness, and expansion;
- symbolic execution, paths, frontiers, branches, loops, and invariants;
- contracts and modular verification;
- memory, permissions, resources, ownership, views, frames, effects, aliasing,
  snapshots, and old state;
- how profiling attributes work and how to interpret a report;
- how expansion rewrites a proof and why replayability is the boundary;
- what audit checks beyond ordinary verification;
- supported C0, C fragments, undefined behavior, and definedness.

Reuse accurate material from `docs/proof-workflow.md`, `docs/click-core.md`,
`docs/memory-model.md`, and the current basic and intermediate chapters. A
concept page should explain one coherent model rather than become an alternate
syntax inventory.

## Internals

Document the current implementation architecture for contributors who need to
change Click. Cover at least:

- repository and module map;
- parser, validation, elaboration, and lowering;
- Surface Click and Kernel Click representations;
- proof goals, proof objects, certificates, focus, branches, joins, and
  continuations;
- smart planning versus simple checking and the exact trust boundary;
- kernel primitives, rules, symbolic execution, assumptions, and memory
  reasoning;
- persistent data structures, memory derivation DAGs, snapshots, and important
  representation invariants;
- instrumentation, deterministic work budgets, deadlines, profiling,
  expansion, audit, and diagnostic boundaries;
- CLI and fixture entry points;
- testing layers, `scripts/check.sh`, mdtests, examples, scaling regressions,
  and the feature-development workflow;
- where and how to add a language form, tactic, kernel rule, CLI option, or
  library symbol without leaving the reference stale.

Distill accurate current-state material from `docs/kernel.md`,
`docs/separation-logic.md`, `docs/advanced/memory-dag.md`,
`docs/advanced/verification-efficiency.md`, and
`docs/advanced/proof-object-api.md`. Do not present chronological progress notes
or abandoned designs as the current architecture. Preserve historically useful
design records outside the normative published reference or rely on Git history
after confirming that no unique current invariant would be lost.

## Verified examples and source fidelity

Every normative syntax, tactic, and library example must be checked by Click.
Prefer one of these approaches, in order:

1. Include a focused snippet from a passing mdtest or example project.
2. Extract a named region from a passing fixture at documentation build time.
3. Add a documentation-example harness that parses and verifies explicitly
   marked blocks in `docs/` with deterministic bounds.

Do not paste a second untested copy of a substantial example. Test negative
examples against their intended focused diagnostic. Keep tutorial-sized
motivation out of exhaustive lookup entries when a link to a concept or guide
is clearer.

When documentation exposes an unsupported true claim, missing simple tactic,
unreplayable smart success, timeout, huge diagnostic, or source pattern that
requires unnatural C, stop the documentation slice and follow the tooling
stability and issue policy in `AGENTS.md`. Do not weaken or rewrite C to obtain
a green documentation example.

## Documentation tooling and gate

Add bounded, reproducible documentation checks to `scripts/check.sh` and CI:

- build the mdBook with a repository-pinned tool version;
- reject missing pages in `docs/SUMMARY.md` unless explicitly unpublished;
- reject broken local links and anchors;
- run the public-surface coverage inventory checks;
- verify exact source-backed declarations, CLI synopses, and marked examples;
- lint structural Markdown properties such as one H1, ordered heading levels,
  language tags on fenced blocks, and meaningful image alternative text;
- enforce the ratcheted subset of the Click documentation style rules.

Use a prose linter such as Vale for mechanically enforceable Google-style and
Click-terminology rules. Introduce it in an advisory or changed-files mode,
then ratchet converted technical pages to required checks; do not turn the
initial legacy warning count into an unreviewable bulk rewrite. Check external
links in a separate scheduled or explicitly networked job so ordinary local
correctness does not depend on remote availability. Local links and anchors
remain part of the deterministic gate.

Generated HTML must have working navigation and search, readable code on
narrow screens, visible focus states, semantic heading order, and accessible
link text. Keep visual customization small until the information architecture
and content are stable.

## Intended regressions

### Public-surface completeness

Add a synthetic public language form, tactic, CLI option, or stdlib declaration
without a reference inventory entry. The documentation coverage test must fail
with the exact missing stable identifier. Remove an implementation item while
leaving its inventory entry; the test must report the stale entry.

### Standard-library synchronization

Change the signature of a fixture stdlib declaration without updating its
reference. The documentation check must fail rather than render stale copied
syntax. The real inventory must initially expose and then close the current
three-symbol documentation gap.

### CLI synchronization

Add or rename a fixture CLI option in the authoritative command metadata. The
reference synopsis or option-coverage check must fail until the corresponding
entry is updated. The test must not execute a child Click process or scrape
stderr.

### Verified documentation examples

Break a normative Click example in a documentation fixture. The ordinary gate
must fail with the page or source-region identity. A documented negative
example must fail if it unexpectedly passes or if its focused diagnostic
changes.

### Site integrity

Add a missing relative page, stale anchor, skipped heading level, duplicate H1,
or unlisted published page to a fixture documentation tree. The relevant
bounded check must reject it with a concise path and location.

### Authorship boundary

The technical-documentation landing page must contain the AI-authorship
disclosure and identify the human-written guide as a separate work. A link to
the guide is required only after that guide exists. Reference restructuring
must not move or rewrite a future human-authored file unless the user explicitly
adds it to scope.

## Execution order

Complete this issue in independently reviewable green slices:

1. Inventory all existing pages and public surfaces; settle stable identifiers,
   the local style contract, the authorship disclosure, and the target
   navigation without rewriting the corpus.
2. Add the documentation build, local-link, structure, and coverage substrate
   with focused regressions.
3. Build the CLI and tactic references, where the public surface is relatively
   bounded and already has strong source material.
4. Split and complete the language and C0 references, including grammar and
   precedence.
5. Build the source-backed standard-library reference and glossary.
6. Consolidate the concept pages.
7. Distill the current internal architecture and remove progress-log material
   from the normative site.
8. Perform a complete inventory audit, terminology pass, Google-style pass,
   link/build/accessibility check, and rendered-site review.

For each slice, preserve existing accurate content, add the relevant coverage
or example regression, run the focused checks, and run `scripts/check.sh` before
integration. Keep incomplete migrations in the task worktree. Do not leave the
primary checkout with a half-moved navigation tree.

## Decisions to confirm before long autonomous work

The implementation can start with the recommended defaults below, but confirm
them before the work reaches the affected slice:

1. **Human guide identity:** reserve a separate top-level "Guide" entry and
   choose its final name and location only when the human document exists.
2. **Versioning:** document the current `master` behavior only for now. Do not
   copy the corpus into release-version directories until Click has a concrete
   multi-version support commitment.
3. **Disclosure placement:** put the full AI-authorship disclosure on the
   technical landing page and a short provenance note in the contributor style
   page, not on every reference page.
4. **Historical design records:** distill current invariants into Internals and
   remove chronological progress logs from published navigation. Preserve a
   separate design record only when it contains enduring information not
   recoverable from Git history.
5. **Stability labels:** describe everything the ordinary parser and CLI accept,
   while labeling supported, experimental, compatibility-only, deprecated, and
   internal surfaces explicitly. Acceptance by the parser alone must not imply
   a stability promise.
6. **Publishing:** make the mdBook output publishable, but leave hosting,
   domains, analytics, and deployment credentials to a separate authorized
   task.

## Acceptance criteria

- The rendered site is organized as Technical reference, Concepts, and
  Internals, with a reserved and clearly separate identity for a future
  human-written guide.
- The technical landing page clearly says that the reference is AI-written and
  AI-maintained, states its accuracy and exhaustiveness goals, and does not
  imply that the future human guide has the same authorship or voice.
- Authored source remains conservative Markdown and mdBook remains the renderer
  for this work; the site title and introduction no longer frame all technical
  documentation as a linear book.
- A tested bidirectional inventory accounts for every supported public language
  construct, tactic and variant, CLI command and option, standard-library
  declaration, and glossary term.
- Language reference includes syntax, validation and semantics, explicit
  precedence and associativity, Surface/Kernel/C-fragment distinctions, C0
  coverage, and supported or unsupported status.
- Tactic reference documents every simple, smart, structural, and control-flow
  form with its state transition, failure, replay, expansion, and profiling
  behavior.
- CLI reference has a synchronized page for `verify`, `profile`, `expand`, and
  `audit`, including all accepted targets, options, defaults, output, exit
  behavior, and relevant environment variables.
- Standard-library reference documents every symbol in
  `stdlib/prelude.click`; exact declarations cannot drift silently, and the
  current three missing symbols are covered.
- The glossary is sufficient for the stated programmer-without-prover-
  experience audience and uses the same canonical terms as the rest of the
  corpus.
- Concepts explain verification, proof construction and checking, symbolic
  execution, memory and resources, expansion, profiling, and auditing without
  duplicating the lookup reference.
- Internals describe the current system, proof objects, kernel and trust
  boundary, important representations and invariants, module ownership,
  tooling architecture, tests, and extension paths without presenting progress
  logs as current design.
- Every normative Click example and documented failure is backed by a passing
  deterministic fixture or an equivalent checked source include.
- `scripts/check.sh` and CI build the documentation and enforce bounded local
  link, structure, example, source-synchronization, and coverage checks.
- All technical-reference headings and navigation use sentence case, the local
  style overlay follows the Google Developer Documentation Style Guide, and a
  final rendered review finds no broken navigation, inaccessible structure, or
  unclassified legacy page.
- Every existing documentation page has been retained in an appropriate home,
  deliberately replaced, moved to a clearly non-normative historical location,
  or removed because its accurate content exists elsewhere; no page disappears
  merely as a side effect of restructuring.
- `scripts/check.sh` passes from an unpiped run in the task worktree.
- Delete this issue and its `issues/README.md` entry only after the complete
  reference, its synchronization regressions, documentation tooling, rendered
  review, and authorship disclosure land together in coherent green commits.
