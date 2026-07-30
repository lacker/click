# Click design review — ranked issues

*Recovered verbatim from the session that produced it (2026-07); referenced by
`handoff.md` as "the design review." Like `handoff.md`, this file is
intentionally untracked; delete it once its contents are absorbed into issues.
Note: items 9–12 were fixed on branch `claude/engineering-debt`, merged to
master 2026-07-29; the top soundness items in tier 1 were fixed on master
before the handoff. Line numbers refer to the tree at review time.*

## Top tier: soundness of the trust chain

**1. The kernel's theorem-minting API can be used to certify false statements.**
Three related holes: (a) `c_verified_function_contract_claim` (api.rs:2277)
strips all Implies hypotheses off a proof without checking them, and matches
the target function only by name/signature/source-body — not by executed body
or contract — so a theorem proven under arbitrary caller-chosen assumptions
about function F with contract C1 can certify F′ with a stronger contract C2,
whose ensures then get injected as certified facts at every call site.
(b) `certify_c_function_execution_paths_from_outcomes` (api.rs:2213) and
`prove_c_function_satisfies_specification_from_symbolic_path` (api.rs:2253)
are pub and mint theorems from caller-supplied outcomes with zero checking —
passing empty facts yields an unconditional false theorem, contradicting
docs/kernel.md's "callers cannot construct arbitrary theorems."
(c) `wrap_proof_facts` (reasoning.rs:3613) silently drops non-assumable
verification conditions from the minted proposition, so a Theorem object is
only trustworthy if every consumer separately remembers to check a
side-channel obligations vector. "Megakernel" tolerates bugs, but these break
the property that a Theorem means anything at all — the untrusted Click layer
already calls these endpoints.

**2. Two genuine logic bugs in the reasoning engine.**
`Assumptions::proves` proves ∀x.P(x) by proving P(x) with x free under
ambient assumptions, with no freshness/eigenvariable check
(assumptions.rs:2765) — if a fact mentions the bound variable's id, false
universals are provable. And fresh-variable soundness generally rests on
conventions: callers supply variable_start seeds, opaque calls hard-code
Variable(8_000_000 + call) namespaces (functions.rs:444), and a pointer
returned by an opaque call gets a fresh block name that
blocks_proven_distinct treats as aliasing nothing (primitives.rs:1689) —
wrong for a callee that returns its own argument.

**3. The C model quietly diverges from real C.**
Struct layout uses packed running-sum offsets with no alignment padding
(syntax.rs:540) while pointers are 8 bytes — `struct { int32 a; int32* p; }`
puts p at offset 4 where every LP64 compiler puts it at 8. Verified layout
facts can be true of the model and false of the compiled program. Relatedly,
unknown pointee types silently default to int32/4-byte width (eval.rs:366)
instead of erroring. For a tool whose goal is verifying real libraries,
model-vs-reality divergence is a soundness issue in the only sense that
matters.

## Second tier: the language can't yet meet its own premise

**4. The C0 parser can't parse realistic C, so sources must be rewritten to be
verified.**
Every if requires an else (syntax.rs:820) — 49 of 269 mdtests carry no-op
`else { p[j] = p[j]; }` padding. No comments (a `//` dies with "expected
expression, got Slash"), no unary minus (`return -1;` fails), no declaration
initializers (`int32 i = 0;` fails), no `a->b->c` chains (field struct-types
are parsed then discarded, syntax.rs:515). Each restriction is defensible for
C0, but together they mean the sidecar premise — verify the C file as it
exists — fails on essentially any real file, and the error messages never
name the restriction.

**5. Kernel Click leaks wholesale into user-facing proofs.**
The flagship examples are full of undocumented kernel spellings:
`load_int32(owner)`, `load_int32_pointer((owner + 2))`, `*(owner + 1)`, and
"a pointer field is two int32 cells" ranges like `owner[0..4]`
(examples/owned-vector/vector.click). `grep load_int32 docs/` finds nothing.
Users must write Kernel Click while the docs pretend Surface Click exists;
diagnostics also speak kernel terms. This directly fails the roadmap's own
Milestone 2 "done" criterion and will get worse when real ABI layout lands.

**6. Proofs are write-only: exact-spelling matching, positional indices, and
order-sensitive closers.**
apply/step/fold/frame require facts in the verifier's exact internal spelling
(mdtests/theorem_apply_requires_exact_fact.md,
simple_statement_step_requires_exact_prerequisite.md) — `x > 0` doesn't match
premise `x >= 0`. Statements are addressed as `statement(5).entry` by
preorder index and `choose(k from requirement 0)` by position, so any edit to
the C body or contract renumbers and breaks scripts. Grouped proofs are
one-shot and order-sensitive: a `simp()` before the enabling `have` fails
permanently with no retroaction (mdtests/grouped_post_tactics_respect_order.md).
Together these couple every proof to source coordinates and internal normal
forms — a refactor of one contract invalidates dozens of scripts.

**7. Verbosity with no abstraction mechanisms: ~5:1 spec-to-code and
copy-paste as the only reuse.**
owned-string: 130 lines of C need 691 of Click; vector.click repeats a nearly
identical 18-fact `step using` block four times. There's no way to name a
fact-set, no parameterized composite states (empty_vector/nonempty_vector
duplicate four owns clauses each), no frame rule over composite bodies (every
fold re-proves invariants a store couldn't have disturbed), no module/import
system — int32_equality_transitive is copy-pasted verbatim into 5 of 6
example projects, and the stdlib is one 92-line prelude. At json-c scale this
proof style is untenable; this is the biggest language-design gap on the
roadmap's critical path.

**8. Three overlapping concept families answer "may I touch this memory,"
with inconsistent sub-syntax.**
`loadable(...)`, resource verbs (views/owns/consumes/produces), and effects
clauses (mutable/immutable) are all range-over-pointer clauses with subtly
different roles; the docs say owned resources imply loadability, yet mdtests
routinely state both. `owns X` vs `consumes X; produces X` are two spellings
of the same contract. `loadable(p, 12)` counts bytes while `loadable(p[0..n])`
counts elements; `mutable_field(...)` is used throughout examples but
essentially undocumented. Whether you need `separate(...)` depends on which
verb family you happened to use. This concept-to-power ratio is the
language's main learnability problem.

## Third tier: implementation architecture

**9. No source positions exist anywhere in either frontend.**
ClickError is a bare message string (click.rs:1405); C0SyntaxError likewise;
the Click parser reports "at token N" by raw index (parser.rs:2788); C
tokenization discards line/column before parsing. Because the AST is
span-free, expansion.rs maintains a second, independent lexer that re-scans
raw source to locate tactics (expansion.rs:448) — two tokenizations that must
agree forever. Spanned tokens would fix user diagnostics and delete the
shadow lexer; the roadmap itself says "diagnostics are a design surface."

**10. proof.rs is a 20,518-line monolith built on hidden-global control flow.**
replay_linear_tactics is ~2,040 lines handling 20+ tactic variants inline;
functions routinely take 13-14 positional arguments; ~3,000 lines of
proposition/expression evaluators are duplicated four ways across
checking/lowering/proof (checking.rs:944 vs checking.rs:4057). Worst pattern:
tactic expansion works by planting a thread_local! probe, re-running full
verification, and aborting via a sentinel error-message string compared by
text (proof.rs:2539, proof.rs:2586), with the top-level driver silently
consulting the hidden global. Similar patterns kernel-side: semantic
decisions keyed on "local:"/"havoc:" string prefixes of block names
(eval.rs:2565), and provability that depends on leftover thread-local fuel
(assumptions.rs:50) — same input can verify or fail depending on prior work
on the thread.

**11. Performance timebombs in the term representation and the test harness.**
Every symbolic memory load embeds a full CMemory snapshot inside the term
(primitives.rs:60); these giant terms are BTreeMap keys and get deep-compared
in linear fact scans on hot paths — super-quadratic as specs grow. proof.rs
has 649 `.clone()` including 72 of whole CStates. Downstream symptom: the
examples suite alone burned 14+ CPU-minutes before I stopped it, and all 269
mdtests run serially inside a single #[test] that aborts at first failure
(mdtests.rs:27) — no parallelism, no full failure report, selection only via
ad-hoc env vars.

**12. The tooling doesn't enforce its own stated guarantees, and the four
binaries have drifted copies of everything.**
todo.md's audit contract requires re-expansion byte-identical checks and
branch-outcome comparison; audit_site (click-audit.rs:621) implements neither
and verifies against a warm retained session rather than "from normal
inputs" — so the corpus-wide enforcement tool for the certificate-replay
invariant checks a weaker property. parse_source_location, parse_duration,
format_duration, and the child-watchdog loop each exist 3-4 times across the
binaries with already-diverged semantics (audit's inline location parser
skips the one-based validation; mdtests rejects bare-number durations the
binaries accept). And there is no whole-file verify command at all —
click-verify demands file:line:column, while the documented workflow ("apply
the output and run normal verification") has no CLI to run.

## Honorable mentions

- while-invariant rule checks preservation in only one condition-fork context
  and against pre-body state (api.rs:2633) — currently test-only but exported.
- 35 panic!/unreachable! sites in proof.rs reachable from user-dependent data
  (e.g. proof.rs:20043) turn diagnosable proof bugs into crashes.
- Logically identical propositions differ in well-formedness:
  `(lo..hi).any(|k| p[k] == x)` is memory-safe to state, the equivalent
  explicit exists with and guards is not.
- Vocabulary churn in docs: "execute_rest() is legacy spelling for
  execute_rest()" (separation-logic.md:265), close_invariants() used in
  examples but absent from the tactic inventory, ~30 tactics with
  near-synonym clusters (step/execute_step/execute_until/execute_rest/...).
- click-profile parses its own child's stderr by exact whitespace field
  counts — format drift silently produces a false-green report.

## How I'd group the discussion

Items 1-3 are "does a Click proof mean anything" and are worth fixing even
under megakernel philosophy since they're trust-chain and model-fidelity
issues, not kernel-complexity issues; items 4-8 are the language-design
debates (4 and 7 are the ones blocking the json-c north star); items 9-12 are
engineering debt where the highest-leverage single move is probably spans +
structured errors (9), since the shadow lexer, bad diagnostics, and
stringly-typed sentinels all hang off it.
