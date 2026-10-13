# SMT-backed automation with kernel-checked certificates

Priority: P1.

Soundness: not soundness. This is automation. Solver search is untrusted.
Every result becomes a certificate that the existing kernel checks, so the
work changes neither the trusted base nor what verifies.

Proof size, automation and proof workflow are the parts of the
[launch design review](design-review.md) that matter most. Its items P1–P4,
W4 and W5 depend on this issue. This issue makes `auto`
call an SMT-style decision procedure to find proofs, and makes Click turn each
result into a certificate that the kernel checks. This is the "hammer" pattern
used by Isabelle's Sledgehammer, SMTCoq and Lean's `omega`/`linarith`.
Changes to `simp` itself wait until stage 1 is measured.

## Decision: an in-house solver

Decided 2026-10-12. Click builds its own decision procedures instead of
calling Z3 or cvc5. They sit behind an interface narrow enough that an external
solver can be plugged in later, for fragments that justify one.

The main reason is expansion. A procedure Click owns emits Click's own
certificate steps, so `auto` always expands into checked simple steps. An
expanded proof never calls the solver again: it checks quickly and gets the
same verdict on every machine. External solvers emit large, version-specific
proofs that Click would have to reconstruct. The in-house route also avoids
shipping a C++ solver, and the solver's search stays under Click's
deterministic work budgets.

The stage-1 design is [design/smt-auto-stage1.md](../design/smt-auto-stage1.md).

## Comparison class

Dafny and Verus are the usual reference for proof size, but neither uses
separation logic for heap reasoning:

- **Dafny** frames the heap with `reads`/`modifies` sets.
- **Verus** gets separation from Rust ownership, and needs explicit tracked
  permissions only for raw pointers.

The fair comparison for C is separation-logic tools that use SMT for their
pure reasoning: VeriFast, Viper, CN and RefinedC. All of them pay a resource
bookkeeping cost. This issue targets the pure-reasoning gap, which accounts
for most of Click's proof size. In one rbtree repair arm, about 600 of 1,377
lines are pure reasoning, against about 100 lines of resource fold/unfold.

## Violated invariant

Click's priorities are, in order:

1. C, C++ and Rust;
2. uncooperative existing code;
3. fast verification of large files without trial and error.

The third priority is not met. Today `by auto;` means exactly
`execute(); simp();`, and `simp` is a heuristic normalizer with fixed limits
("up to eight variables", "nested at most twice",
`docs/reference/tactics/index.md`). Several kinds of reasoning are done by
hand:

- linear arithmetic, transitivity chains and width bridges are written out
  step by step;
- facts that `simp` cannot find are restated in `using { ... }`;
- `arithmetic_certificate` blocks are written out by hand.

The result is that proofs are 6–120 times the size of the C they verify
(design-review item P1), and getting a step through takes trial and error.
SMT-based tools such as Dafny and Verus do this reasoning without being
asked. Click can do the same while keeping its rule that only the kernel
decides a verdict.

## Design

The solver only searches; it never decides. A step is accepted only when its
reconstructed certificate checks in the kernel, as every smart tactic's
expansion does today.

- **Flakiness and slowness affect search only.** Once a certificate exists,
  checking it is fast and deterministic. The solver runs again only when the
  cached certificate no longer checks, for example after the C or the
  specification changes.
- **Failure decomposes.** When the solver gives up, the author splits the
  goal with `have` or a case split, and each piece goes back to `auto`.
  Click executes C one step at a time, so its queries are small and local.
  Dafny-style verification instead sends one large formula per method.
- **The proof stays inspectable.** `click expand` prints the reconstructed
  certificate.

## Stages

Do the stages in order. Each stage is useful on its own.

1. **Arithmetic and equality oracle.**
   - For linear integer arithmetic, the solver returns Farkas coefficients.
     Click's `arithmetic_certificate` steps (`premise`, `scale`, `add`) are
     already Farkas proofs, so the translation is direct.
   - For equality, congruence closure returns a path of rewrites, which Click
     emits as `rewrite` steps.
   - The oracle sits behind `auto`, which is the only entry point.
2. **Premise selection from the unsat core.** The solver reports which
   premises it used. Click fills in `using { ... }` itself, so authors no
   longer restate propositions to cite them. This removes most of the need
   for named facts (design-review P4).
3. **Certificates outside the sidecar.** The source keeps saying `by auto;`.
   The reconstructed certificate is stored in a cache or lock file next to the
   sidecar, like the existing import locks. `click verify` checks the cached
   certificate and, on a miss, searches again within a work budget. Sidecars
   stay small, and unreadable expansions stop being committed (design-review
   W4). Per-claim caching also speeds up large proofs (design-review W5).
4. **Mathematical integers in specifications** (design-review P2). Solvers
   handle unbounded linear integer arithmetic well and machine-width
   arithmetic poorly. Unbounded specification integers help both the solver
   and the author.

## Out of scope

- Full reconstruction of solver proofs that use quantifiers. Start where
  certificates are simple.
- Induction and recursive resource predicates. These stay in the tactic layer
  (`fold`, `unfold`, induction), because solvers are weak at them.

## Risks

- **Reconstruction is the main engineering cost.** Stage 1 limits it to
  Farkas and congruence certificates.
- **Solver output must not affect a verdict** except through a checked
  certificate. With an in-house solver this holds by construction, and it
  must still hold for any external solver plugged in later.
- **Search must stay bounded.** A solver call runs under a deterministic work
  or time budget, and the call fails locally and promptly when the budget is
  exhausted. A slow solver run is a tooling failure under `CLAUDE.md`, not a
  successful slow run.
- **Scaling.** Each query must be built from the explicit premises and the
  affected proof state, never from project-wide or path-wide state
  (`docs/internals/verification-efficiency.md`).

## Baseline

Measured 2026-10-12 at `52a77c2d`, release build, `click verify` on one
sidecar. The fourth column is the share of each file that stage 1 targets:
linear arithmetic, `to_integer` bridging, congruence and constructor
equalities.

| Case | Lines | Time | Stage-1 target |
|---|---|---|---|
| `examples/rust-byte-sum/sum.click` | 184 | 0.29 s | about 120 lines of the loop body: bridges, `arithmetic() using` and transitivity |
| `examples/bounded-pool/bounded_pool.click` | 845 | 2.1 s | five hand-written `arithmetic_certificate` blocks plus their bridge `apply`s |
| `examples/rbtree-erase/rbtree_erase_color_flips_red_all.click` | 4,236 | 22.9 s | the 222 one-line rewrite equalities in each arm |

In the first two cases, most of the arithmetic is bridging between machine
integers and `Integer`, through theorems such as `int32_less_equal_to_integer`
and `int32_add_to_integer`, not linear reasoning itself. Stage 1 therefore
includes a machine-integer bridge theory; see the design.

## Results so far

| Case | Before | After | What remains explicit |
|---|---|---|---|
| `examples/bounded-pool/bounded_pool.click` | 845 lines, 2.1 s | 455 lines, about 2 s | resource folds and authority steps; every arithmetic lemma is `by auto` |
| `examples/rust-byte-sum/sum.click` (milestone 3, with operation bridging) | 184 lines, 0.29 s | 68 lines, about 1.4 s | memory transport for the read, fold laws (`peel`), loop control, and one conjunct of the invariant restated so it can be cited |
| `examples/rbtree-erase/rbtree_erase_color_flips_red_all.click` (milestone 4, the `Context::Right` red-inner-child arm, lines 2020–2180) | 18 of its 23 one-line rewrite `have`s explicit; 24,926 bytes; about 21–23 s for the file | each of the 18 is `by auto`; 22,980 bytes (5,612 → 4,945 tokens); about 23.5 s | three-rewrite chains the attempt budget misses, `unfold` after a rewrite once the `simp` closures are spent, and `plug` equalities over whole contexts |

Milestone 4 adds equality reasoning as a bounded search for a chain of `rewrite`
steps, not the congruence closure the design describes. It already covers most
one-line rewrite proofs. On two random samples of 20 of the file's 470 one-line
`have P by { rewrite(..); assumption(); }` or `..; normalize(); }` proofs,
`by auto` closes 18 and 13; `simp` alone closes 13 and 9. The remaining misses
are mostly facts with no source spelling where the proof stands (in the
largest arms, most of a 200-equality component: facts over values the proof
named with `let`, `fold` or match bindings, and C values read before a later
write), and chains that need `unfold` or injectivity. Congruence closure does
not lift the spelling limit: its certificate is also written as `rewrite`
steps. In a theorem with no C, a `have`, an `intro` antecedent and an `obtain`
body are spelled as written, as a proof `if` case already was, so `auto` can
rewrite by them.

The longer run time is solver search, all within the smart budget.
`click audit` expands all 19 sites into simple steps that verify without the
solver. The certificate cache
(stage 3) is what removes this search from ordinary verification.

## Where Click's proofs are longer

Measured 2026-10-13: nonblank annotation or proof lines per nonblank line of
code. VeriFast files count their `/*@ @*/` and `//@` lines, lemma proofs
included; CN's tutorial states its recursive lemmas and proves them in Coq,
so those proofs are not counted; Click counts every `.click` line of the
project.

| Program | VeriFast | CN | Click |
|---|---|---|---|
| Singly linked list | 6.9 (`examples/lists.c`, 15 lines of C) | 1.3 | 1.2–1.5 (`linked-list`, `allocated-linked-list`, `marked-linked-list`) |
| Queue, stack, doubly linked list | 2.0–3.4 | 1.1–1.8 | 1.9 (`ring-buffer`) |
| Binary tree against a model | 2.3 (`sorted_bintree.c`), 4.8 (`vstte2012` tree) | — | 3.5 (`binary-tree`), 14 (`modeled-binary-tree`) |
| Red-black tree | none public | none public | 23 (`rbtree-insert`), 33 (`rbtree-erase`) |

On ownership-only proofs Click is level with both. The gap is in proofs
against a functional model, and it is the pure reasoning, not resource
bookkeeping: `tree_rotate_left` in `modeled-binary-tree` spends about 10 of
its 49 lines on `unfold`/`fold`, which VeriFast also writes as `open`/
`close`, and most of the rest stating facts as `have`s that SMT tools derive
without being asked. A one-line `have` proved `by auto` saves nothing; the
lines go away only when `auto` runs where obligations are discharged and the
`have` can be deleted.

The next steps, in order:

1. **`auto` closes contracts.** Done: `by auto;`, an omitted proof, and a
   script that ends with a claim open close with `auto` instead of `simp`
   alone. In `tree_rotate_left` the two `have`s proving the `ensures` become
   one `apply` line.
2. **Spell `apply` conclusions.** A rewrite needs its equality as source
   text; a fact `apply(...)` adds has none, so `auto` cannot rewrite by a
   lemma's conclusion. The rbtree erase file has 197 `apply`s.
3. **Unfold definitions applied to constructors.** `heap_right(Node(...))`
   and similar facts are stated by hand in every arm of a tree proof.

Each step is judged by deleting `have`s from the examples and checking that
the proofs still verify.

## Regression

Prototype stage 1 behind `auto`, then measure the change in
proof size and verification time on three cases:

- `examples/rust-byte-sum`, the loop and arithmetic case;
- `examples/bounded-pool`, the overflow-bridging case (about 270 lines of
  `arithmetic_certificate` today);
- one `examples/rbtree-erase` case file, the scale case.

Rewrite each case to rely on the oracle, while keeping the C unchanged. Add
mdtests for:

- a linear-arithmetic goal proved by `have P by auto;` with no hand-written
  certificate;
- a congruence goal proved the same way;
- a goal the solver cannot prove, which fails promptly and boundedly with an
  actionable diagnostic.

## Acceptance criteria

- `auto` proves linear integer arithmetic and congruence goals through the
  solver. Every accepted step is justified by a kernel-checked
  certificate, which `click expand` prints.
- Verification with a warm certificate cache does not call the solver, and its
  verdict is deterministic.
- A solver timeout, crash or wrong answer can only cause a local, bounded
  failure. It can never cause acceptance.
- The three regression cases shrink, and the measured sizes and times are
  recorded in this file. If they do not shrink substantially, record that,
  and rule on stages 2–4 before continuing.
- `docs/reference/tactics/index.md` describes the oracle, its budget and the
  certificate cache.
