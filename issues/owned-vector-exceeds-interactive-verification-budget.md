# Owned-vector verification exceeds the interactive budget

The fully verified `examples/owned-vector` project takes about 19.4 seconds
warm on the development machine. It passes the unchanged 30-second project
gate, but is far too slow for an interactive edit/verify loop and provides an
important larger integration workload for the verification-efficiency
contract.

A 2026-08-13 baseline profile reported:

```text
19.410s total
  simple          3.546s  (528 completed, 7ms average, 470ms max)
  smart          10.104s  (138 successful attempts at 134 source sites)
  control          702ms
  certification   1.344s
  verifier core   3.626s
```

No completed simple tactic crossed the 500ms tail guard. The initial dominant
cost was therefore valid proof planning, especially in `vector_grow` and
`allocated_vector_push`, rather than one pathological simple checker.
Expanding eleven independently verified hotspots reduced a current profile to
about 13.1 seconds and reduced smart time to about 3.6 seconds without
increasing aggregate simple replay. No smart site now exceeds 300ms. Continue
expanding only newly measured material hotspots before attributing the residual
engine cost.

The residual is already visibly mixed. `allocated_vector_push` spends about
2.8 seconds outside its claim tactics (roughly 0.7 seconds certification and
2.1 seconds verifier core), while `vector_grow` retains roughly 2.6 seconds of
smart planning. Once the material smart sites are expanded, the former must be
reprofiled against the indexed fact/resource and stable-identity issues rather
than hidden by further proof-source growth.

On 2026-08-13, checked whole-claim expansion removed every dynamically executed
smart tactic from the project. (One unused theorem still contains a syntactic
`simp`; the profile records zero smart attempts.) The warm profile is now:

```text
7.119s total
  simple          2.133s  (274 completed, 8ms average, 458ms max)
  smart               0ms  (0 attempts)
  control           625ms
  certification   1.338s
  verifier core   2.870s
```

This is the pure-simple scaling regression the issue was missing. Expansion
removed the planning and mixed-script gate costs, but the project remains above
the five-second target. The dominant residual is now unambiguously engine work:
`allocated_vector_push` takes about 3.56 seconds, including about 0.89 seconds
of certification and 1.49 seconds of verifier core. Its profile shows both an
approximately 0.70-second independent checked execution and an approximately
0.70-second contract body symbolic execution, so the existing checked-artifact
reuse path is not matching this realistic function. `vector_replace_if` also
spends about 0.57 seconds almost entirely in verifier core, and the broad
resource operations still show a roughly 0.42-second framed-load derivation
walk and a roughly 0.24-second representation check.

## Regression

Keep the complete project as a wall-clock integration workload. Every engine
optimization motivated by it must also add or extend a deterministic scaling
regression over the isolated ambient-state axis it fixes. Expansion changes
must be made only from a fully verified proof, must verify in place, and must
not make simple replay materially slower.

## Acceptance criteria

- Warm verification is comfortably interactive, targeting under five seconds
  on the development baseline.
- All material successful smart hotspots have replayable expansions, and the
  expanded project remains a fixed point under the expansion audit.
- No simple tactic crosses its deterministic or 500ms tail guard.
- Remaining certification and verifier-core work is attributed to named
  operations and protected by deterministic scaling gates.
- No speedup weakens a contract, changes the C, raises a budget, skips
  independent certification, or caches a result under deep linear identity
  comparison.
