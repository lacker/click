# Launch design review: open critiques

Priority: P1.

Soundness: soundness-adjacent. This file is a tracker. Items M1 (no
independent checker), M2 (no written semantics) and M3 (`memcpy` reading under
`viewable`) are trust questions without a known false acceptance. Each item that becomes a reproduced false acceptance is filed in
`bugs/` with its own label.

Depends on [smt-auto.md](smt-auto.md). Items P1–P4, W4 and W5 are expected to
be fixed by its stages; rule on them after its stage-1 measurements land.
Also depends on [simplify-step.md](simplify-step.md), which now holds the
critique that "simple" `step()` is not simple (formerly W3).

On 2026-10-12 Click was reviewed the way an expert launch audience would
review it, from four sides: the surface language, the proof and tactic
workflow, the memory and resource model with its trust story, and a
newcomer's first hour. This file lists every critique that review raised.
Each one gets an explicit ruling, **fix** or **wontfix**, with the reason; a
critique is not dropped by being forgotten. Delete an item when its fix,
regression and documentation land, or when it is ruled wontfix and the
ruling and its reason are moved to `design/proof-language-rulings.md` (or
another design document where the ruling belongs). Delete this file when it
is empty.

Every item starts as **Decision: open**. Record the maintainer's ruling in
place before work starts.

Documentation has two audiences. The repository and `docs/`, the AI
reference, are written for AI readers: an agent asked to evaluate or use Click
reads them, so they must be precise, complete and honest about limits.
Human-facing material (the top of the README, the guide in `guide/` and a
public website) is written by the maintainer, so critiques of human onboarding,
such as jargon load and positioning against other verifiers, are the
maintainer's and are not tracked here.

## Violated invariant

A reader of Click's launch material can verify a small function in their own
C code in an hour, understand what was proved and what was trusted, and
write proofs whose size and fragility are in proportion to the code. Each
item below is a place where that is not yet true, or where a launch reviewer
is likely to say it is not.

## Why Dafny and Verus proofs are so much shorter

Context for items P1–P4. Dafny and Verus generate one verification
condition per method and hand it to an SMT solver (Z3), which does linear
arithmetic, congruence closure, case splitting and quantifier instantiation
without being asked; the user writes specs, loop invariants and occasional
hints. Their specs use mathematical integers; Dafny is designed for
verification and Verus inherits aliasing and memory safety from Rust's type
system. Click deliberately trusts no external solver: every step is checked
by its own kernel, smart tactics expand into simple checkable steps, search
is bounded and deterministic, and it verifies arbitrary existing C, so memory
safety, undefined behavior and aliasing are its own obligations. That buys
reproducible verdicts and inspectable proofs, and costs length. Published
SMT-based systems work reports proof-to-code ratios in the low single digits;
seL4 in Isabelle is roughly 20x, about Click's own target
(`docs/internals/verification-efficiency.md`). The way to close most of the
gap without giving up checkability is the Lean `omega`/`linarith` model:
decision procedures that search freely and emit certificates the kernel
checks.

## P. Proof size and automation

### P1. Proofs are far larger than the code

Today: `examples/rbtree-erase` is 39,047 lines of `.click` for 322 lines of
C (about 120x, six times the 20x target in
`docs/internals/verification-efficiency.md`);
`rbtree_erase_color_flips_red_all.click` alone is 518 KB with lines over
1,300 characters. `examples/rust-byte-sum` proves a 9-line loop in about 184
lines; `examples/modeled-binary-tree` proves the 12-line `tree_contains` in
about 100. `examples/arena/arena_cells.click` is 5,537 lines for 279 lines
of C.

Proposed fix: items P2–P4 and P6, plus a published proof-to-code budget per
example that the gate reports.

Done when: the examples meet a stated budget, or the budget and the reason
for exceeding it are published.

Decision: open.

### P2. Spec arithmetic is machine arithmetic

Today: `+` in a specification is the C operation and is partial
(`docs/reference/language/index.md`, "an int32 fold's `+` is partial in
specifications"). Proofs bridge with `to_integer`, width-specific lemmas
(`int64_less_equal_transitive` and about 150 more in `stdlib/prelude.click`)
and hand-written `arithmetic_certificate` blocks: about 270 lines of
`examples/bounded-pool/bounded_pool.click` show counters do not overflow.
ACSL, Dafny and Verus specs use mathematical integers by default.

Proposed fix: specification arithmetic is over `Integer` by default; C
semantics are written explicitly where a spec means them
([smt-auto.md](smt-auto.md) stage 4).

Done when: decided, and if fixed, the examples shrink accordingly.

Decision: open.

### P3. Little automation behind `simp`

Today: symmetric equalities, transitivity and width bridges are proved by
hand (`modeled_binary_tree.click`, `have left_model == l.model by {
rewrite(l.model == left_model); normalize(); }`), and `simp` is described by
heuristic limits ("up to eight variables", "nested at most twice",
`docs/reference/tactics/index.md`).

Proposed fix: [smt-auto.md](smt-auto.md) stage 1: a solver-backed decision
procedure for linear integer arithmetic plus congruence closure behind `simp`
and `arithmetic`, whose results are reconstructed as kernel-checked
certificates.

Done when: decided; if fixed, the procedure's certificates are kernel-checked
and a representative example shrinks.

Decision: open.

### P4. Facts cannot be named

Today: "`have` takes no label, and a later step cites it by restating `P`"
(`docs/reference/tactics/index.md`). Long propositions are restated in every
`using { ... }` (`examples/rust-byte-sum/sum.click`), and `rewrite(` appears
about 6,900 times across rbtree-erase and arena.

Proposed fix: `have h: P` and `using { h; }`. Unsat-core premise selection
([smt-auto.md](smt-auto.md) stage 2) removes most citations, so rule on this
after that stage.

Done when: decided; if fixed, documented with an mdtest, and
`mdtests/have_takes_no_label.md` updated.

Decision: open.

### P5. Copy-paste across case files and sidecars

Today: `rb_erase` has 11 per-case contracts and no general one. The general
erase-color repair proof's left and right arms (about 1,380 lines each) are
mirror images. C++ caller sidecars repeat callee contracts
(`examples/basic-cpp/with_restore_caller.click`).

Proposed fix: [design/proof-reuse.md](../design/proof-reuse.md):

- R2: one general contract per function, including one general `rb_erase`
  contract with a theorem that its cases are exhaustive.
- R3: automatic unfolding of recursive spec functions.
- R4: automatic opening and closing of resources.
- R5: one script for several arms.

Decision: open.

### P6. Loop proofs restate facts

Today: invariants restate immutable facts and held views
(`examples/rust-byte-sum/sum.click`), iterations end with explicit
`step(); step(); step(); close_invariants();`, and identical facts are
re-`have`d after steps (`examples/rbtree-erase/rbtree_erase_black_spine.click`).

Proposed fix: facts about values a step cannot change carry across steps
automatically; the back edge closes implicitly.

Decision: open.

## W. Proof workflow and tooling

### W1. Proofs are tied to C statement positions

Today: `execute_until(statement(54))`, `read(0)`, `assignment(i, 1)`,
`at(statement(4).entry, ...)` and `f.loop(N)` count positions in source
preorder (`docs/concepts/proof-workflow.md`); adding one statement renumbers
every later index, and expanded certificates hard-code them. There is no
migration tool.

Proposed fix: name program points by source (C labels, call names,
patterns, comments), or ship `click migrate` that renumbers a sidecar after
a C edit.

Decision: open.

### W2. The tactic set is large and overlapping

Today: about 57 forms over 41 tactic words (`docs/reference/tactics/index.md`);
`simp`, `normalize`, `assumption`, `arithmetic`, `extract`, `rewrite` and
`transport` overlap.

Proposed fix: a documented core of about 15 tactics, with the rest marked as
expansion output or specialized.

Decision: open.

### W4. Expansion output is hard to read and gets committed

Today: expanded arithmetic certificates use numbered nodes and repeat
identical blocks (`mdtests/bubble_sort3_two_pass_sorted.md`); committed
expansions keep noise such as `have 0 == 0 by normalize();` and runs of
`assumption();` (`examples/vector-push/vector_push.click`).

Proposed fix: named, deduplicated certificate nodes; keep the
smart source and cache certificates instead of committing expansions
([smt-auto.md](smt-auto.md) stage 3).

Decision: open.

### W5. Performance limits the large proofs

Today: rbtree-insert takes about 118 s on 20 cores and rbtree-erase minutes
(`tests/examples.rs`), both outside the gate; the erase README reports about
43 sidecar lines per second; a full audit takes about 20 minutes
(`docs/internals/testing.md`).

Proposed fix: per-claim incremental caching by default
([smt-auto.md](smt-auto.md) stage 3); budgets reported in work units.

Decision: open.

### W6. Some diagnostic lines still print kernel notation

Facts, goals, rejected requirements, evaluated sides, search candidates and
the proof context now print in Click or C syntax (`old(g[0]) < 100`,
`(uint32)n <= 1073741823u32`, `viewable(p[1..2])`), with reads of other
memories as `at(<state A>, ...)` defined after the report. `--trace-proof`
keeps its typed notation by design.

Today: a loop-carried value inside the body prints as the iteration's entry
value, `at(statement(N).entry, i)`, and a refused C operation names an address
a local holds through that local (`alias->mu`, `*shared`, `p[i].y`). What
remains:

- A callee's result no local holds prints as `<unnamed A>` (`pure facts:
  [<unnamed A> == -56]`); its only spelling is a translation temporary.
- A pure theorem's `Integer` binder prints as `<unnamed A>` in a
  conversion-condition refusal (`<unnamed A> + 1`): that refusal's names come
  from the machine-typed values only.
- A heap allocation no live local holds prints as `<pointer A>`, mostly in an
  `ensures` check after the function returned: the outcome state has no
  locals, and the execution's recorded snapshots that held the pointer are not
  part of that check's names.
- A store at a constant offset into a struct-typed global or local prints as
  `g+8` in memory-history text: a field name needs the store's width checked
  against the field, which `SourceCell` does not carry.

Proposed fix: name a callee's result through the snapshot after its call and
an allocation through the snapshot that last held it, where the outcome check
can cite that snapshot; spell constant offsets as fields where the width
matches.

Decision: in progress.

## L. Surface language

### L1. Too many words, several with more than one meaning

Today: the word index has about 200 words
(`docs/reference/language/grammar.md`). `fold` is a tactic, a range method
and resource construction; `unfold` opens a function call, switches a
predicate's transparency branch-wide, consumes a resource layer, and mints or
burns a counted member; `count` is a keyword and a prelude function;
`function` starts both a pure function and a C contract; `as` has four uses.

Proposed fix: one meaning per word, e.g. `reveal` for predicates and
`mint`/`burn` for counted members; move certificate step names out of the
general word index.

Decision: open; the maintainer will revisit it after L2–L7.

### L2. No spec `bool`

Today: truth values in specs are `int32` (`list_contains<T>(...) -> int32`
in `stdlib/prelude.click`); a theorem exists only to show a `0`/`1` result
is `1` when not `0` (`examples/modeled-binary-tree`).

Proposed fix: a specification `bool`.

Decision: fix (maintainer, 2026-10-13): a specification `bool`.

### L4. Rust and C++ specs still read like C

Today: a Rust sidecar's pure function takes `bytes: const uint8*, end:
uint64` and casts `(int32)bytes[k]` (`examples/rust-iterators/sum.click`);
lengths compare with `4u64`, `bool` results are specified as
`if ... { 1 } else { 0 }` (`docs/reference/rust.md`); a C++ `bool` is
`early != 0`.

Proposed fix: Rust types and `as` throughout Rust sidecars, including pure
functions; `bool` results as `bool`.

Decision: fix (maintainer, 2026-10-13), after L2: Rust types, `as` and `bool` throughout Rust sidecars.

### L5. Resource clauses overlap

Today: `consumes X; produces X;` beside `owns X`; per-field `owns` lists;
frames restated after `produces`.

Proposed fix: `owns *s` for whole structs; infer frames for produced cells.

Decision: open.

### L6. Fold syntax is heavy and generics are fully applied

Today: `fold(tree_at(result), { model: ... }, { left: lower, right: z })`;
`List<struct tree_node*>::Nil`; the reference shows both `as { ... }` and
`let {...} = unfold(...)`.

Proposed fix: infer constructor type arguments and default child maps by
name; one documented unfold binding form.

Decision: fix (maintainer, 2026-10-13): infer constructor type arguments and default child maps by name; one documented unfold binding form.

## M. Memory model, semantics and trust

### M1. There is no independent proof checker

The trusted base is now listed in `docs/concepts/trust.md`: kernel (about
254,000 lines of Rust), obligation construction, the C front end and target
model, importers, prelude theorems applied without re-checking, and `extern`
contracts. Replacing the README's kernel-design essay is the maintainer's
human-facing work.

Today: `click expand` and `click audit` re-check proofs with the same kernel
and lowering, so a bug there is invisible to them; there is no serialized proof
object and no independent checker.

Proposed fix: serialize proof objects and write a small independent checker
that re-checks them.

Decision: inventory done; independent checker open.

### M2. No written semantics or soundness argument

Today: the resource algebra and loan ledger are described in prose
(`docs/internals/separation-logic.md` calls its notation "explanatory";
`docs/internals/stable-views.md` lists laws without proof).

Proposed fix: a paper-level operational semantics and a model of views and
loans, with fold/unfold and loan recovery argued sound against it.

Decision: open.

### M3. Several read-permission notions and no fractions

Today: `views` (call-scoped loans), `viewable` (bounds only), reads granted
by a folded composite, and reads from match-arm selection. The trusted
`memcpy` contract reads its source under `viewable` alone
(`docs/internals/byte-representation.md`), against "external loads require a
covering viewed or owned memory resource". No fractional permissions, so no
reader-writer pattern.

Proposed fix: fractional or counted read permissions; fold `viewable` into
them; reconcile `memcpy`.

Decision: open.

### M4. Field-less resources hide a record

Today: a field-less `pair(p)` keeps its child's fields "in a record the
author does not write" (`docs/reference/language/index.md`); the alternative
was dropped because the kernel treats a field-less body as a function of its
arguments in about thirty places (`design/proof-language-rulings.md`).

Proposed fix: require explicit fields, or show the record in diagnostics and
expansion. This revisits a recorded ruling.

Decision: open.

### M5. Aliasing and place syntax are inconsistent

Today: `owns a->n` and `owns a->n[0..1]` differ
(`design/place-based-resource-clauses.md`). The docs now agree that a
contract's `owns` clauses are disjoint from each other and from its `views`
clauses, and that `separate(...)` is needed only between views and
`viewable` facts.

Proposed fix: finish the place-based design.

Decision: open.

## N. Newcomer experience

### N1. Maintainer launch actions

Today: the human-only top of the README calls Click "a new programming
language" and opens with the kernel-design essay, and no release has been
tagged, so the installers fail.

Proposed fix: the maintainer writes the README top (a one-line pitch; the
essay moves to a design document or the website) and tags the first release.

Decision: fix (maintainer).

### N5. C++ and Rust look like research demos

Today: both need a repository checkout and custom importer builds
(`examples/basic-cpp/README.md`, `examples/basic-rust/README.md`); the C++
example is `int increment(int& value)`. The AI reference now labels both
experimental (`docs/reference/coverage.md`) and keeps migration history out of
`docs/reference/rust.md`.

Proposed fix: ship the exporter and Charon with the installer; a C++ example
beyond a scalar reference.

Decision: open.

### N7. The repository root mixes product and process

Today: `design/`, `issues/`, `bugs/`, `AGENTS.md` and `CLAUDE.md` sit at the
root, next to the maintainer's `guide/`.

Proposed fix: move process material under one directory or a separate
repository; decide what the launch repository presents.

Decision: open.

## Strengths the review credited

Recorded so fixes do not trade them away: verification of unchanged source
with pinned hashes; deterministic verdicts from work budgets; smart search
never trusted, expansion and audit re-checked; documentation tied to passing
fixtures; precise statements of what is proved (termination, undefined
behavior, `diverges`); readable resource verbs with the write footprint equal
to ownership; allocation lifetime separate from access; candid scoping such
as Adler-32's "remains unproved".
