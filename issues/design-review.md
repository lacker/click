# Launch design review: open critiques

Priority: P1.

Depends on [smt-auto.md](smt-auto.md). Items P1–P4, W4 and W5 are expected to
be fixed by its stages; rule on them after its stage-1 measurements land.

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

Today: the 22 color-repair increments that
`rbtree_erase_color_flips_red_all.click` subsumes (29,160 of 39,582 lines,
including the 24 inline copies of the `__rb_change_child` proof) are retired,
and their mutations run against the general proof (R1). `rb_erase` has 11
per-case contracts and no general one. The general repair proof's left and
right arms (about 1,380 lines each) are mirror images. C++ caller sidecars
repeat callee contracts (`examples/basic-cpp/with_restore_caller.click`).

Proposed fix: [design/proof-reuse.md](../design/proof-reuse.md):

- R1: retire superseded increments. Done.
- R2: one general contract per function.
- R3: automatic unfolding of recursive spec functions.
- R4: automatic opening and closing of resources.
- R5: one script for several arms.

Decision: R1 ruled fix and done; R2–R5 open.

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

### W3. "Simple" `step()` is not simple

Today: `step()` is labelled simple yet runs "with every fact in the proof
context visible" (`docs/reference/tactics/index.md`); the work to make it
simple is paused (`issues/simplify-step.md`).

Proposed fix: finish `issues/simplify-step.md`, or reclassify `step()`.

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

### W6. Diagnostics print kernel notation

Today: refusals print terms such as
`int32 <(load A=read<Bits32>(snapshot#1, pointer=value#1), 100) is true`
(`mdtests/a_claim_true_in_one_alias_case_is_refused.md`) and
`left side evaluated to load(bytes)`. Many messages are good ("the store to
`a[j]` may have written it ... state `i != j`").

Proposed fix: render every fact and term in Click or source syntax.

Decision: open.

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

Decision: open.

### L2. No spec `bool`

Today: truth values in specs are `int32` (`list_contains<T>(...) -> int32`
in `stdlib/prelude.click`); a theorem exists only to show a `0`/`1` result
is `1` when not `0` (`examples/modeled-binary-tree`).

Proposed fix: a specification `bool`.

Decision: open.

### L3. Two conversion families and C-fragment precedence

The precedence half is fixed: a comparison operand whose outermost operator
is `&`, `^` or `|` must be parenthesized, since C and Click group
`x & 1 == 0` differently, and the `aligned(p, n)` sugar is documented as
`(address(p) & (n - 1)) == 0`.

Today: `(uint32)x` keeps the low bits, `to_uint32(x)` needs a range proof,
and implicit return conversion follows a third rule
(`docs/reference/language/index.md`).

Proposed fix: one checked conversion family plus an explicit wrapping one.

Decision: precedence ruled fix (reject unparenthesized mixing); conversions
open.

### L4. Rust and C++ specs still read like C

Today: a Rust sidecar's pure function takes `bytes: const uint8*, end:
uint64` and casts `(int32)bytes[k]` (`examples/rust-iterators/sum.click`);
lengths compare with `4u64`, `bool` results are specified as
`if ... { 1 } else { 0 }` (`docs/reference/rust.md`); a C++ `bool` is
`early != 0`.

Proposed fix: Rust types and `as` throughout Rust sidecars, including pure
functions; `bool` results as `bool`.

Decision: open.

### L5. Resource clauses overlap and the docs disagree

Today: `consumes X; produces X;` beside `owns X`; per-field `owns` lists;
frames restated after `produces`; the docs disagree on whether `owns` grants
access (`docs/concepts/spec-state.md` vs `docs/reference/language/index.md`).

Proposed fix: reconcile the documents; `owns *s` for whole structs; infer
frames for produced cells.

Decision: open.

### L6. Fold syntax is heavy and generics are fully applied

Today: `fold(tree_at(result), { model: ... }, { left: lower, right: z })`;
`List<struct tree_node*>::Nil`; the reference shows both `as { ... }` and
`let {...} = unfold(...)`.

Proposed fix: infer constructor type arguments and default child maps by
name; one documented unfold binding form.

Decision: open.

### L7. Small spellings vary

Today: `by auto;`, `by simp;` and `by { simp(); }`; `witness { k: x }`
without `;`; both `#` and `//` comments; `old(x)` beside
`at(function.entry, x)`.

Proposed fix: rule on each, keeping sugar only where it is documented as
sugar.

Decision: open.

### L8. The language reference reads like a changelog

Today: `docs/reference/language/index.md` is about 3,000 lines with "this
slice", "not yet" and mdtest citations throughout; core and edge cases are
mixed.

Proposed fix: a short core reference separate from the full reference.

Decision: open.

## M. Memory model, semantics and trust

### M1. The trusted computing base is large and the README argues for it

Today: `src/kernel` is about 406K lines of Rust (with tests) and
`src/surface` about 261K, part of which is trusted
(`docs/internals/architecture.md`, `docs/internals/kernel.md`); there is no
independent certificate checker; prelude axioms are applied without
re-checking. The README's opening essay rejects the small-kernel principle.
Nine kernel bugs were filed from one soundness review.

Proposed fix: serialize proof objects and write a small independent
checker that re-checks them; until then publish a trusted-base inventory with line counts, and
replace the README essay with it.

Decision: open.

### M2. No written semantics or soundness argument

Today: the resource algebra and loan ledger are described in prose
(`docs/internals/separation-logic.md` calls its notation "explanatory";
`docs/internals/stable-views.md` lists laws without proof).

Proposed fix: a paper-level operational semantics and a model of views and
loans, with fold/unfold and loan recovery argued sound against it.

Decision: open.

### M3. The rbtree claim may be read as overstated

Today: the launch claim is "Click verified the Linux kernel rbtree" over
"an unchanged, pinned upstream `lib/rbtree.c`" (`issues/README.md`). The
fixtures are extracted bodies over a hand-written header shim
(`examples/rbtree-insert/rbtree.h` defines `NULL`, `likely`,
`__always_inline` and `WRITE_ONCE`); importing the real headers is P2
(`issues/linux-rbtree-inline-helpers.md`,
`issues/kernel-scale-preprocessing.md`); erase is about 25 per-case
sidecars.

Proposed fix: state the claim exactly ("extracted bodies under a modeled
header environment"), list the shim as trusted, and show one top-level
`rb_erase` contract.

Decision: open.

### M4. Several read-permission notions and no fractions

Today: `views` (call-scoped loans), `viewable` (bounds only), reads granted
by a folded composite, and reads from match-arm selection. The trusted
`memcpy` contract reads its source under `viewable` alone
(`docs/internals/byte-representation.md`), against "external loads require a
covering viewed or owned memory resource". No fractional permissions, so no
reader-writer pattern.

Proposed fix: fractional or counted read permissions; fold `viewable` into
them; reconcile `memcpy`.

Decision: open.

### M5. Field-less resources hide a record

Today: a field-less `pair(p)` keeps its child's fields "in a record the
author does not write" (`docs/reference/language/index.md`); the alternative
was dropped because the kernel treats a field-less body as a function of its
arguments in about thirty places (`design/proof-language-rulings.md`).

Proposed fix: require explicit fields, or show the record in diagnostics and
expansion. This revisits a recorded ruling.

Decision: open.

### M6. Aliasing and place syntax are inconsistent

Today: `docs/reference/language/limitations.md` says to add `separate(...)`
for possibly aliasing pointers; `docs/internals/separation-logic.md` says
owned ranges are exclusive by composition. `owns a->n` and `owns a->n[0..1]`
differ (`design/place-based-resource-clauses.md`).

Proposed fix: state that `separate` is needed only for views and
`viewable`; finish the place-based design.

Decision: open.

### M7. C semantics are narrow and the summary is stale

Today: one target (x86-64 LP64 little-endian), fork/join and mutex
concurrency only, read-only unions; `docs/concepts/what-click-proves.md`
lists a scalar set without `int64`/`uint64`, which
`docs/reference/language/limitations.md` supports.

Proposed fix: one coverage matrix (undefined behavior, provenance,
concurrency, target), kept in sync mechanically.

Decision: open.

### M8. Soundness triage is inconsistent

Today: "An unsound rule is P1" (`issues/README.md`), yet "Give private
static storage sound ownership" is P2
(`issues/private-static-helper-ownership.md`), and `old(result)` is accepted
with the argument that it is not unsound
(`issues/result-accepted-in-entry-snapshots.md`).

Proposed fix: a soundness label on issues with a written argument, and a
re-triage.

Decision: open.

## N. Newcomer experience

### N1. The README does not show Click working

The part of the README that agents may edit now opens with a ten-line C file,
its sidecar, and a `click verify` transcript (`examples/clamp/`, checked by
`readme_quick_start_is_the_clamp_example` in `tests/examples.rs`), followed by
install, documentation, and a short contributing section; the merge-queue
instructions for agents stay in `docs/internals/contributing.md`.

Remaining: the human-only top of the README still calls Click "a new
programming language" and opens with the kernel-design essay.

Proposed fix: a maintainer replaces line 3 with a one-line pitch and moves
the essay to a design document.

Decision: fix.

### N3. No guide for verifying a function in your own project

Today: the only unchanged third-party C example proves `json_c_version()`
returns a constant (`examples/jsonc-existing-source`); compiler import is a
separate mode documented mostly for C++ (`docs/reference/cli/import.md`).

Proposed fix: "verify one function in your project": include paths, `-D`
flags, contracts for libc calls, and what to do when C0 refuses a construct.

Decision: open.

### N4. The default C target is the Linux kernel's

Today: the default is `x86_64-linux-kernel` with unsigned plain `char`
(`docs/reference/language/c0.md`); userspace code needs an explicit
`target`.

Proposed fix: default to userspace, or print the target on every run.

Decision: open.

### N5. Docs contradict themselves and are stale

The contradictions are fixed: `docs/reference/language/c0.md` no longer claims
`click verify` prints the default target, the README installs from source
and states that no release or crates.io package exists, and
`tests/documentation.rs` checks that every version the README names is the
`Cargo.toml` version.

Remaining: no release has been tagged, so the installers fail.

Proposed fix: tag the first release before launch (a maintainer action).

Decision: fix.

### N6. Jargon load, and internal documents in the user book

Today: "smart", "kernel", "frontier", "certificate" and "proof unit" appear
throughout user docs; the glossary is about 1,200 lines;
`docs/reference/language/limitations.md` opens with parser nesting budgets
and addresses "agents"; the book's summary includes the rbtree launch
roadmap and the worker authority protocol.

Proposed fix: separate a user guide from internals; a ten-term glossary on
the first-proof page.

Decision: open.

### N7. C++ and Rust look like research demos

Today: both need a repository checkout and custom importer builds
(`examples/basic-cpp/README.md`, `examples/basic-rust/README.md`); the C++
example is `int increment(int& value)`; `docs/reference/rust.md` opens with
retired-schema history.

Proposed fix: label both alpha up front; ship the exporter and Charon with
the installer; keep migration history out of user docs.

Decision: open.

### N8. No positioning against other tools

Today: `docs/concepts/proof-landscape.md` maps features to Frama-C,
VeriFast, CBMC and Dafny but does not say when to choose Click; Kani, Verus,
Prusti and Creusot are not mentioned.

Proposed fix: a "Click and other verifiers" page, honest about weaknesses.

Decision: open.

### N9. The repository root mixes product and process

Today: `design/`, `issues/`, `bugs/`, `AGENTS.md` and `CLAUDE.md` sit at the
root; `docs/index.md` says the docs are AI-written and a human-written guide
will follow.

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
