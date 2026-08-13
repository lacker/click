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

A rejected reuse prototype changed independent certification to start from a
canonical contract resource spelling so its checked artifact matched final
contract certification. It reduced owned-vector to about 5.65 seconds, but made
binary-tree exceed its 30-second project deadline. Removing proof-entry branch
facts also broke certified outcome pairing. Reuse therefore needs a kernel
certificate relating definitionally equivalent entry resource states and a
checked composition of complementary path frontiers; substituting the caller
state before certification is not semantics/performance neutral.

That kernel boundary is now implemented for the bounded cases. Checked
executions may be rebased only when the concrete entry state is exact and
non-recursive ghost resource contexts are proved definitionally equal; two
complete executions under opposite polarities of one exact entry condition may
also be composed. Incomplete partitions and extra unproved premises still
force fresh execution, while recursive resources skip the equivalence probe
entirely. Focused regressions count body executions for every acceptance and
rejection case.

This removes the second approximately 0.7-second body execution from
`allocated_vector_push`. A current warm profile is about 6.50 seconds, with
certification reduced from roughly 1.35 seconds to 0.65 seconds and
`allocated_vector_push` certification reduced from roughly 0.90 seconds to
0.20 seconds. Binary-tree remains at its 4.2-second baseline; an unrestricted
recursive-resource probe was measured at 9.5 seconds and is explicitly
excluded. The remaining vector cost is about 2.16 seconds of simple replay,
2.89 seconds of verifier core work, and 0.64 seconds of control overhead.

Explicit-frame attribution now isolates its resource transition. The
`allocated_vector_push` frame's roughly 0.4-second tail is almost entirely
return-resource core projection, specifically proving that a post-state
`owner->data` view matches an older snapshot spelling. Premise lowering and
exact lookup are no longer the material cost. Exact-only core deduplication is
not valid—it leaves stale views across frees—so this remaining tail needs a
faster certified snapshot-equivalence path.

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
