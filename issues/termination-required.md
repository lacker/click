# Require termination by default

## Priority

P1. Click's default judgment is partial correctness: a verified `ensures`
holds only if the function returns, and nothing requires that it does. A
verified function can therefore contain a loop that never exits, and every
caller's conclusions silently become conditional on a return nobody proved.
That is the wrong default for a verifier whose claim is that the verified C
does what its contract says. Divergence must be something a contract admits
out loud, not something every contract permits.

This blocks [the concurrency demo](concurrency-demo.md). A `pthread_join` on a
worker with no termination evidence may never return, so the fork/join slice
cannot state what its parent proves until a worker's contract says whether it
terminates. The unfinished slice is parked on the branch
`claude/concurrency-demo-slice2-parked`; its
`design/concurrency-probes/PARKED.md` lists what to fix on resume.

## What holds today, so it is not redone

Safety is not conditional on return, and this issue does not change that.
Undefined behavior, memory authority, and the footprint are checked on every
step of every execution prefix, and a loop body is proved for an arbitrary
iteration. A non-returning loop that writes memory its function does not own
is refused at the store. Only the `ensures`, and liveness itself, are
conditional.

The termination machinery already exists behind an opt-in. A C `decreases`
clause on a function asks Click to certify termination of the whole function:
every reachable loop and recursive component must be ranked, every callee must
have termination evidence of its own, and the kernel records that evidence
separately from `CVerifiedFunctionRule`. Measures are an `int32` ranking
expression, a lexicographic tuple of them, or a structural resource binder.
See "Optional C termination" in `docs/reference/language/index.md` and
`docs/concepts/loops-and-invariants.md`. This issue inverts the default and
makes the judgment modular; the loop and recursion ranking checks it relies
on already exist.

## Violated invariant

A verified function returns on every execution its `requires` admits, unless
its contract explicitly says it may not. Today the reverse holds: termination
is certified only for a function that asks, and the absence of a `decreases`
clause means "unknown", which callers cannot distinguish from "terminates".

## Intended regression

This verifies today and must be refused, with a diagnostic that names the
unranked loop and offers the two repairs: a `decreases` clause or the
`diverges` marker.

```c
int wait_for_zero(int x) {
    while (x != 0) {
    }
    return 1;
}
```

```click
int32 wait_for_zero(int32 x) {
    ensures result == 1;
} by {
    loop {
        invariant 0 == 0;
        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

This regression and its first two companions are in place, as
`required_termination_refuses_an_unranked_loop_and_its_caller` and
`required_termination_spreads_diverges_to_callers` in
`src/surface/tests/project_tests.rs` and `mdtests/diverges_perpetual_loop.md`.
Three companions are required:

- the same function declared `diverges`, with `loop diverges`, verifies;
- a terminating caller of the marked function is refused, and the diagnostic
  names the callee;
- a counted loop, `for (int i = 0; i < n; ++i)`, verifies with no
  hand-written measure once inference lands, and `click expand` prints the
  `decreases` clause it chose.

## Decided design

**The judgment is local descent.** Every function has a measure in a
well-founded order, and every call site proves that the callee's declared
measure, at the actual arguments, is strictly below the caller's measure at
entry. That is the whole checked rule. Soundness is one induction on the
measure. The trusted core runs no call-graph pass, computes no components, and
keeps no project-wide termination state, so a location-scoped run needs only
what it already reads: each callee's declaration, of which the measure and the
marker are part, exactly as its `ensures` is.

This replaced the whole-project pass that found components by pairwise
reachability and closed a fixpoint over them, which was roughly cubic in the
function count and could not serve a scoped run.

**Call-DAG height is plan data, never source.** For ordinary code whose
calls form a DAG the measure is the function's height in that DAG. An
untrusted planner assigns each function a natural number, the longest path in
the syntactic direct-call graph, in one linear pass. The kernel checks only
that each call site's callee height is below the caller's, or equal with the
user's measure descending; it trusts nothing about how the numbers were
chosen, as with today's untrusted `CFunctionTerminationPlan`. Heights have no
source spelling. A number written in source goes stale when a helper is added
deep in the graph, and a relative spelling ("above `g`") is well-founded only
if acyclic, which would put a global check back in the trusted core. `click
expand` and `click audit` may display heights. Height assignment is a
deterministic computation, not a search; its one failure is a cycle, the
diagnostic names the cycle, and the repair is a `decreases` clause on its
members. A whole-project run has one plan covering every call and is the
authoritative judgment; a scoped run takes callee heights as assumptions, as
it already takes callee contracts.

**The user explains termination exactly where there is a real cycle.** A loop
carries a loop `decreases`. A recursion, direct or mutual, carries a
function-level `decreases`; the user writes only the component that descends
around the cycle, never the height. Both spellings exist today; unsupported
recursive shapes stay tracked in [recursion.md](recursion.md). A recursive
function with no measure is refused under the new default, the same as an
unranked loop.

**Indirect calls use the same rule.** A named contract is the only
declaration an unknown callee has, so it carries a `decreases` clause over its
own parameters, the same keyword a function uses. A call through the pointer
proves descent against the contract's measure, and forming the contract at
`&g` proves that `g`'s measure fits under it. A dispatch table whose handler
`i` re-dispatches only to entries `j < i` is then provable, which no
syntactic graph analysis can decide, and `f` passing itself to `apply`
unchanged is refused because no measure satisfies the three constraints. A
pointer the verifier resolves statically, as a `const` callback table does,
is a direct call. Do not approximate indirect edges with an address-taken or
signature-matched call graph: a false cycle there has no repair.

**The marker is `diverges`, in the signature.** It sits after the parameter
list beside `throws`, because it is the same kind of thing: an effect that is
part of the function's type, not one of its promises.

```click
int32 serve(int32 fd) diverges {
    ensures result == 0;
}
```

Like `throws int32`, it declares a possibility, not a certainty. A named
contract is a signature too, so a callback's termination status goes in the
same position and is compared when the contract is formed at `&g`. A loop has
no signature, so the loop marker goes on its head: `loop diverges { ... }`.
Every loop carries `decreases` or `diverges`, so an intentionally perpetual
loop is named and a forgotten measure in an already marked function is still
caught.

It is contagious, and unlike `throws` there is nothing that catches it: a
function must be marked exactly when one of its loops is, a callee is, or a
call has no descent proof. Those conditions are local, so an unjustified
marker is refused at no extra cost. A marked function keeps today's semantics:
safety on every prefix, `ensures` if it returns. A perpetual service loop is
the intended use.

**Externs.** An `extern` contract follows the same rule as any other
function. Unmarked, it asserts that the function returns, on the same trust as
its `ensures`; marked, its callers inherit the marker. The parser accepts the
marker on `extern` blocks and still rejects `decreases` there, since there is
no body to rank, and an `extern` marker is never refused as unjustified,
because the declaration is all that is known. `pthread_join` is a modeled call
whose return depends on the worker's contract; that rule belongs to the parked
fork/join slice.

**Simple tactics first.** Every measure must be expressible as an explicit
clause with no inference; loop measures that Click infers expand to one. Do
not make the kernel guess measures.

**Loop inference, to make migration tractable.** Infer the measure for a loop
whose guard compares an induction variable with a bound the body does not
write and whose step moves the variable toward the bound. The corpus has about
250 `while` loops and about 20 `for` loops, so the recognizer must key on the
counted shape and not on the `for` keyword. Anything else asks the user for a
clause; search completeness is a non-goal.

**Scalability.** Per-function termination work is the function's own call
sites and loops. Height inference reads the forward call closure
syntactically and must be linear in it; record that in
`docs/internals/verification-efficiency.md` as the one output-sensitive
exception.

## Open questions

- Whether a named contract's height can be inferred. It can when the sites
  that form it are syntactically visible; otherwise callback contracts need
  an explicit level.

## Out of scope unless migration needs it

Measures over model values. Today a loop measure is an `int32` expression
over the loop's own unaddressed locals, or structural descent into a
resource's `contains` children. A walk over a DAG ranked by a ghost value,
`rank[cur]` over a model sequence, fits neither. Extend the measure language
in this campaign only if a corpus loop cannot be ranked without it; otherwise
it is later work. Either way, a natural terminating loop that today's measures
cannot rank is a finding to report.

## Migration

Every loop and recursive function in `mdtests/`, `examples/`,
`integrations/`, and the documentation's verified examples currently verifies
with no measure. Do not migrate on a long-lived branch. The new rule lands on
master early, behind a switch, and the corpus is burned down against it in
small green commits.

**The switch.** `with_termination_required(|| ...)`, off by default, scoped
to the verification it wraps in the way `with_deadline` is, and reachable as
`click verify --require-termination`. It is not an environment variable or a
child mode. It is temporary: the flip deletes it.

**The pending marker.** A corpus file that does not yet pass with the switch
on says so itself, with a `termination` block holding `pending: <reason>`,
where the reason is the refusal's root cause. The marker is per-file so that
many agents can clear files in parallel without editing one shared list; the
small `examples/` and `integrations/` sets keep a list beside their harness.
The gate holds every unmarked file to the new rule. A marked file is verified
with the switch off, and again with it on, where it must still be refused for
the recorded reason: a marked file that now passes fails the gate until its
block is deleted, so the pending set can only shrink and never goes stale. A
new test is held to the new rule from the day it is written, and the count of
blocks, by reason, is the campaign's progress number.

**Migration commits are green either way.** A `decreases` clause is already
legal and already certified under today's opt-in rule, so a commit that adds
measures to a handful of tests and deletes their `termination` blocks is
valid under both settings. No commit depends on the flip.

**Keep the termination refusal last.** It must run after ordinary
verification, as the current pass does, so an `expect fail` test keeps failing
for the reason it records and does not start failing on a missing measure.

Stages, each a green commit or a short run of them:

1. Done. The `diverges` marker (7f12d1ab); the local-descent judgment with
   planned heights, the marker's contagion and the unjustified-marker
   refusal, the switch, and refusals that carry one machine-readable reason
   (932e13e8). In flight: the pending marker with its ratchet and the seeding
   run, and the scaling regression.
2. Read the seeded counts by reason: unranked loop, unmeasured recursion,
   indirect call, callee, diverging callee. Split the unranked loops into
   counted and other by shape. These counts, not a guess, decide the shape of
   loop inference and what to do next.
3. Counted-loop inference with expansion. Delete the blocks it clears.
4. Measures on named contracts, and the indirect-call descent rule.
5. Grind the remaining buckets by hand in small commits: explicit
   `decreases` clauses, or the marker where divergence is intended. A loop
   that cannot be ranked with today's measures is a finding: report it, leave
   its block in place, and do not mark it `diverges` to get past it.
6. When no block is left, flip the default, delete the switch and the
   pending-marker machinery, and rewrite "Optional C termination" and the
   partial correctness paragraphs in the loops concept page.

## Acceptance criteria

- A function with no marker verifies only with termination evidence for every
  reachable loop, recursive cycle, and callee.
- The marker is required on, and only on, functions that may not return, and
  the refusal for a missing marker names the loop or callee responsible.
- Inferred loop measures expand to explicit clauses that verify unchanged,
  and the kernel checks planner-assigned heights at every call site.
- The whole corpus is green under the new default with no function marked
  `diverges` merely to avoid writing a measure.
- The language reference, the loops concept page, and the limitations page
  describe termination as the default and partial correctness as the marked
  exception.
- A scaling regression shows termination checking stays within the
  verification-efficiency contract across several project sizes.
