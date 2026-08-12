# Budget and deadline truncation masquerade as certificate mismatches

When the whole-project wall-clock deadline expires while a claim's certified
ghost regions are being compared, the failure is reported as a certificate
mismatch instead of a deadline:

```text
execution proof for `tree_rotate_left.contract` path 0 changed more than the
certified ghost regions
  memory snapshots differ
  missing certified resources: [views tree(node[(load(arg-memory@(...)) - v100000)])]
  extra certified resources: [views tree(node[(load(arg-memory@(...)) - v100000)])]
```

The "missing" and "extra" rows print the same resource spelling: the two
sides are equal, but the equality query was cut short by the expired
deadline (cooperative truncation returns a conservative "not equal"), and
the comparison reports the pruned answer as a semantic difference. The same
run with a longer `--time-limit` verifies cleanly, and pristine master
before the deterministic-budget work shows the identical output, so this is
the whole-claim gate's deadline interplay, not a budget or memoization
regression.

This is misleading in exactly the way the always-track list forbids: a user
sees a "certificate failed complete replay" for a proof that is fine, with a
diff whose two sides are byte-identical, and there is no hint that time ran
out. On a loaded machine the default 30-second project deadline puts
binary-tree into this state routinely.

The deterministic work budgets have the same masking problem in other
comparison layers: when `copy3.contract`'s `close_invariants` (148,094 work
units, the corpus's largest simple tactic) runs under an exhausted simple
work budget, the invariant-bundle replay reports

```text
could not replay invariant closer: invariant 1 is missing path goal: ForAll { ... }
```

with a full internal proposition dump, instead of naming the exhausted
budget. Reproduce by setting the simple work budget below 148,094 and
running the `copy3_array_demo.md` mdtest.

## Reproduction

```sh
target/debug/click verify --time-limit 15s examples/binary-tree
target/debug/click verify --time-limit 3m examples/binary-tree   # verifies
MDTEST_FILTER=copy3_array_demo cargo test --test mdtests   # with simple work budget < 148,094
```

## Acceptance criteria

- A comparison that fails only because an ambient deadline or budget
  truncated its reasoning reports the deadline/budget (as tactic budget
  exhaustion already does), never a semantic mismatch.
- A reported resource mismatch never prints an identical missing/extra pair;
  if the spellings agree, the diagnostic must say what actually differed.
- A focused regression drives the ghost-region comparison against an expired
  deadline and asserts the failure names the deadline.
