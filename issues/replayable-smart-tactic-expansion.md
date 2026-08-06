# Make smart-tactic success require replayable expansion

## Problem

Click's smart tactics search for a proof that would be tedious to write by
hand. Their contract is stronger than merely finding a kernel theorem: a smart
tactic must also produce an equivalent proof made from simple tactics, and
that expansion must replay in a fresh verification session. `click profile`
identifies expensive smart tactics, `click expand` replaces them, and `click
audit` checks that this process works throughout a project. If search can
succeed without a replayable expansion, that workflow has a hole.

The source-faithful owned-vector pipeline exposes one instance of the general
problem. `execute_until` can complete smart symbolic execution through the
general `vector_push` call, but certificate reconstruction loses the stable
Surface Click spelling of a public postcondition that relates statement-entry
and statement-exit values. The kernel knows, for example, that the exit
`owner->len` equals the entry `owner->len + 1`; the later surface emitter tries
to rediscover which stored fact and source anchor express each snapshot.
Search can therefore report success before expansion fails to replay.

This must not be repaired only as a special case for modular calls or vector
proofs. Any smart tactic can otherwise repeat the same architectural mistake:
perform semantic search first, discard how the result was obtained, and then
reverse-engineer a source certificate from the final proof state.

## Violated invariant

Smart-tactic success means that the tactic has constructed a replayable simple
certificate. Finding a kernel theorem without retaining enough information to
emit and replay that certificate is not success.

In particular:

- every fact used by a smart proof has stable provenance;
- source statements and entry/exit snapshot identities remain explicit;
- the exact premises, transports, frame witnesses, and proof-producing
  derivations selected by search are retained;
- surface emission does not repeat proof search or guess source spellings from
  an undifferentiated final fact map; and
- an emitted certificate is checked under fresh source lowering before the
  smart tactic, `click expand`, or `click audit` accepts it.

This is shared smart-tactic infrastructure. Each smart tactic may have its own
search strategy, but it should lower its result through the same certified
proof-plan representation and obey the same success boundary.

## Intended architecture

Make smart tactics proof-producing throughout this pipeline:

```text
smart search
    -> structured proof plan with exact provenance and premises
    -> Surface Click made only from simple tactics
    -> fresh replay
    -> success
```

The structured plan should identify the producer of each fact, its source
program point, all relevant memory snapshots, the exact context premises used,
and any transport or framing step required to replay it. The representation
should be general enough for symbolic execution, simplification, automation,
resource reasoning, and future smart tactics; it must not encode only the
current `execute_until` failure.

Surface reconstruction should consume this plan rather than insert candidate
spellings into a global fact map and later choose one. When a certificate needs
a statement-local frame witness, lower the actual emitted proposition in a
fresh source context and select `normalize`, `assumption`, `derive`, or an
explicit `transport` only when that exact step replays. A kernel fact that
normalizes can still lower from `at(entry)` and `at(exit)` spellings to
different memories during fresh replay.

Statement numbering must come from one shared source-layout traversal used by
execution, structural proofs, expansion, and replay. If an older path used a
loop index or synthetic assertion index as a statement index, migrate it
deliberately with regressions rather than changing its interpretation as a
side effect of recording more provenance.

Do not address this by making the C or proof shape friendlier, adding special
surface candidates for the vector example, accepting internal-only
certificates, or teaching `click expand` to tolerate a non-replayable result.

## Intended regressions

### General smart-tactic contract

Add a reusable test harness that runs each expandable smart-tactic fixture in
three modes:

1. verify the original smart proof;
2. expand it completely to simple tactics; and
3. verify the expanded proof in a fresh session.

The harness should reject smart success when certificate construction or fresh
replay fails, and its failure should identify the smart tactic and proof site.
Keep representative fixtures for every distinct smart-tactic implementation,
not merely every surface alias.

### Modular-call snapshot regression

Add a focused three-file fixture with a `struct counter`:

1. `zero(counter)` ensures `counter->value == 0`;
2. `increment(counter)` ensures both its result and the exit field equal the
   entry field plus one; and
3. `pipeline(counter)` calls both modularly and proves `result == 1` and
   `counter->value == 1`.

The pipeline must verify, expand, and replay without manually restating the
callee's mixed-snapshot postcondition.

Keep owned-string, input-cursor, binary-tree, and ring-buffer as compatibility
regressions. They exercise existing source anchors, local frame transports,
and repeated modular calls that the narrow counter fixture does not.

A regression for a new smart tactic is incomplete until it exercises expansion
and fresh replay, not just successful search.

## Acceptance criteria

- Smart-tactic APIs cannot report success without a constructed certificate
  that has replayed under fresh source lowering.
- All expandable smart-tactic implementations use a shared structured proof
  plan, or explicitly justify and test an equally strong proof-producing
  boundary.
- `click profile`, `click expand`, and `click audit` agree about smart-tactic
  identity, success, expansion, and replay.
- The two-call counter regression verifies and expands to a replayable simple
  proof.
- The general-vector pipeline no longer reports search success followed by
  certificate replay failure.
- Public mixed-snapshot postconditions have stable, unambiguous Surface Click
  spellings tied to their source calls.
- Existing `at(statement(...))` proofs retain their meaning, or any deliberate
  migration is explicit and mechanical.
- Adding provenance does not broaden certificate search or cause unrelated
  tactic-budget regressions.
- Owned-string, input-cursor, binary-tree, ring-buffer, the full example gate,
  profile, expansion, and audit pass within their normal budgets.
