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
`docs/concepts/loops-and-invariants.md`. This issue inverts the default; it
does not build a termination checker.

## Violated invariant

A verified function returns on every execution its `requires` admits, unless
its contract explicitly says it may not. Today the reverse holds: termination
is certified only for a function that asks, and the absence of a `decreases`
clause means "unknown", which callers cannot distinguish from "terminates".

## Intended regression

This verifies today and must be refused, with a diagnostic that names the
unranked loop and offers the two repairs: a `decreases` clause or the
explicit may-diverge marker.

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
        preserve by { }
    }
    step();
    simp();
}
```

The proof script is a sketch; adjust it to whatever currently verifies the
function before flipping the default, so the regression records a real
before-and-after. Three companions are required:

- the same function carrying the may-diverge marker verifies;
- a terminating caller of the marked function is refused, and the diagnostic
  names the callee;
- a counted loop, `for (int i = 0; i < n; ++i)`, verifies with no
  hand-written measure once inference lands, and `click expand` prints the
  `decreases` clause it chose.

## Design constraints

**The marker.** One contract-level keyword says a function may not return.
Choose the spelling with the grammar's existing clause style in mind. It is
contagious: a function that calls a may-diverge function, or contains a loop
with no measure, must carry it too. A marked function keeps today's
semantics: safety on every prefix, `ensures` if it returns. A perpetual
service loop is the intended use.

**Simple tactics first.** The checked judgment must be expressible with an
explicit `decreases` clause on every loop and function, with no inference. A
measure that Click infers is a smart feature layered on top: it must expand
to the explicit clause, and `click expand` must print it. Do not make the
kernel guess measures.

**Inference, to make migration tractable.** Most loops in the corpus are
counted loops whose measure is mechanical. Infer the measure for a loop whose
guard compares an induction variable with a bound the body does not write and
whose step moves the variable toward the bound. Anything else asks the user
for a clause; search completeness is a non-goal.

**External and modeled functions.** A declaration with a trusted contract
needs a termination status. Decide the default for library contracts and
which modeled calls may block. `pthread_join` terminates when the worker it
joins has termination evidence; deadlock remains out of scope until locks
exist.

**Recursion.** Function-level measures already exist; unsupported shapes stay
tracked in [recursion.md](recursion.md). A recursive function with no measure
is refused under the new default, the same as an unranked loop.

**Scalability.** Termination checking per function must stay within the
complexity contract in `docs/internals/verification-efficiency.md`: callee
evidence is looked up, never recomputed, and call-graph cycles are found once
per project, not per call site.

## Migration

Every loop and recursive function in `mdtests/`, `examples/`,
`integrations/`, and the documentation's verified examples currently
verifies with no measure. Stage the change so every commit is green:

1. Add the marker and its contagion rule while termination is still opt-in,
   with the regressions above that do not depend on the default.
2. Add counted-loop measure inference with expansion, and measure how much of
   the corpus it covers.
3. Add explicit `decreases` clauses, or the marker where divergence is
   intended, to everything inference does not cover. A loop that cannot be
   ranked with today's measures is a finding: report it, do not mark it
   may-diverge to get past it.
4. Flip the default, and rewrite "Optional C termination" and the partial
   correctness paragraphs in the loops concept page to describe the new rule.

## Acceptance criteria

- A function with no marker verifies only with termination evidence for every
  reachable loop, recursive cycle, and callee.
- The marker is required on, and only on, functions that may not return, and
  the refusal for a missing marker names the loop or callee responsible.
- Inferred measures expand to explicit clauses that verify unchanged.
- The whole corpus is green under the new default with no function marked
  may-diverge merely to avoid writing a measure.
- The language reference, the loops concept page, and the limitations page
  describe termination as the default and partial correctness as the marked
  exception.
- A scaling regression shows termination checking stays within the
  verification-efficiency contract across several project sizes.
