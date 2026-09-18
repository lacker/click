# Require termination by default

## Priority

P1, and nearly closed. The rule landed: termination is now Click's only
judgment for C, and divergence is something a contract admits out loud with
`diverges` rather than something every contract permits. What remains is one
acceptance criterion, counted-loop measure inference; see
"Migration: done, except one criterion" below.

This no longer blocks [the concurrency demo](concurrency-demo.md): a worker's
contract now says whether it terminates, so the parked fork/join slice on
`claude/concurrency-demo-slice2-parked` can state what a `pthread_join`
parent proves. Its `design/concurrency-probes/PARKED.md` lists what to fix on
resume.

## What holds today, so it is not redone

Safety is not conditional on return, and this issue does not change that.
Undefined behavior, memory authority, and the footprint are checked on every
step of every execution prefix, and a loop body is proved for an arbitrary
iteration. A non-returning loop that writes memory its function does not own
is refused at the store. Only the `ensures`, and liveness itself, are
conditional.

Click certifies termination of the whole function: every reachable loop and
recursive component must be ranked, every callee must have termination
evidence of its own, and the kernel records that evidence separately from
`CVerifiedFunctionRule`. Measures are an `int32` ranking expression, a
lexicographic tuple of them, or a structural resource binder. See "C
termination" in `docs/reference/language/index.md` and
`docs/concepts/loops-and-invariants.md`.

## Violated invariant

A verified function returns on every execution its `requires` admits, unless
its contract explicitly says it may not. This now holds. Before the flip the
reverse did: termination was certified only for a function that asked, and the
absence of a `decreases` clause meant "unknown", which callers could not
distinguish from "terminates".

## Intended regression

This is refused, with a diagnostic that names the unranked loop and offers the
two repairs: a `decreases` clause or the `diverges` marker.

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
  `decreases` clause it chose. This one is still missing; inference was never
  built.

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

**Calls through function pointers get a small rule, not an analysis.** No
edge of the direct-call graph says what a pointer call reaches: a function can
hand itself to the helper that calls it, or be stored by one function and
called by another that it calls in turn. The rule is about the address and
not the call. A function whose address is taken, in a body or in a static
initializer, must return without calling through a function pointer itself,
directly or in anything it calls; then no pointer call can re-enter its
caller, and every pointer call returns. A comparator, a visitor, and an
augment callback qualify with nothing written. `f` handing itself to `apply`
is refused where the address is taken. A pointer the verifier resolves
statically, as a `const` callback table does, is covered, because its entries
are addresses taken in an initializer. Do not approximate indirect edges with
an address-taken or signature-matched call graph: a false cycle there has no
repair.

The rare case this refuses, a callback that itself takes callbacks or a
dispatch table whose handler `i` re-dispatches only to entries `j < i`,
terminates for a reason only a measure can state: a `decreases` clause on the
named contract, against which the pointer call descends and under which the
function must fit when the contract is formed at `&g`. Build that when an
example needs it. Until then such a function is refused; it is not marked
`diverges` to get past the rule.

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

**A loop the verifier executed needs no measure.** A loop with no `loop`
block is not summarized: execution runs it concretely, one bounded iteration
at a time, and succeeds only when every feasible path has left it. That
execution is the termination evidence, so a function proved `by auto` over a
constant-bound loop holds with nothing written. This is what "auto infers the
measure" comes to for these loops: there is no invariant bundle for an
inferred measure to join. Landed; it cleared 15 files with no edit.

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

- A `diverges` named contract. The marker parses there, and nothing yet
  refuses applying such a contract inside a function that is not declared
  `diverges`. The kernel knows at the call step which contract it applies, so
  the refusal belongs there. No test uses one yet.

## Out of scope unless migration needs it

Measures over model values. A loop measure is an `int32` expression over the
loop's locals and the memory it reads, or structural descent into a
resource's `contains` children. A walk over a DAG ranked by a ghost value,
`rank[cur]` over a model sequence, fits neither. Extend the measure language
in this campaign only if a corpus loop cannot be ranked without it; otherwise
it is later work. Either way, a natural terminating loop that today's measures
cannot rank is a finding to report.

Migration did need measures that read memory: `while (i < owner->len)` has no
local to measure against, and three grind slices hit it independently. That
is landed, with no change of syntax. Ranking obligations are still built from
the declared C expression, but each read in it is now evaluated by the
ordinary expression evaluator at the iteration's two states.

## Migration: done, except one criterion

The flip landed: termination is the only judgment, and the migration
scaffolding is gone. `with_termination_required`, `click verify
--require-termination`, the per-file ```termination `pending:` marker, the
`TERMINATION_PENDING` list, and their shrink-only ratchet were deleted once
the corpus was green under the rule. Every mdtest, example, and integration
fixture, and the in-process proof fixtures in `src/`, now carries a
`decreases` clause, a `diverges` marker, or a loop the verifier executes
concretely.

Stages 1, 2, 4, 5, and 6 are done. Stage 3 was not built, and it is the only
reason this file still exists:

3. **Counted-loop measure inference.** The plan was to infer the measure for
   a loop whose guard compares an induction variable with a bound the body
   does not write and whose step moves the variable toward the bound, and to
   have `click expand` print the `decreases` clause it chose. The corpus was
   ground out by hand instead, so nothing in the tree infers a loop measure
   today. Until this lands, the acceptance criterion "inferred loop measures
   expand to explicit clauses that verify unchanged" has nothing to hold: it
   is unmet rather than satisfied. The recognizer must key on the counted
   shape and not on the `for` keyword, and the inferred measure must expand to
   an explicit clause that verifies unchanged, per "Simple tactics first"
   above. Search completeness is a non-goal.

The intended regression for stage 3 is the one companion of the three that is
still missing: a counted loop, `for (int i = 0; i < n; ++i)`, verifies with no
hand-written measure, and `click expand` prints the `decreases` clause it
chose. The other two companions are in place.

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
