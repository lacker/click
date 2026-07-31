# owned-vector: forward fix

Status: open (queued; current failure site may move when the
containment prover lands — retest before starting)
Claimed:

Fails in ~13 s at `vector_replace_if.contract` tactic 8: `have`
cannot find `Implies(replace == 0, new == old)` — a propositional gap
over plain variables, no memory in the goal.

History (bisected, see notes/regression-history.md): broke 07-19 at
`9ea6739` "remove replay bookkeeping tactics", BEFORE the certificate
wave; two later events (fail->hang at 919e084, then today's site via
post-break edits) layered on top. Fix forward from the current
message; the 9ea6739 mechanism (deleted execution-point /
opaque-call-counter bookkeeping) says where replay context may have
thinned.

Secondary finding parked here: this example's PASS time exploded
1 s -> ~190 s between 07-15 and 07-19 before any breakage — profile
it once it verifies again.

Repro:
```
CLICK_EXAMPLE=owned-vector cargo test --test examples
```

Done when: owned-vector verifies within budget and de-quarantines.
