# Bounded-pool outcome conjunction has no explicit simple certificate

`examples/bounded-pool` fails ordinary verification:

```text
`pool_init.contract` path 0, tactic 1: `have` failed: post-execution
simplification proved `((0 <= pool->checked_out && pool->checked_out <=
pool->capacity) && pool->checked_out == count(pool_object(pool, _)))`, but
Click has no explicit simple certificate for that derivation
  selected premises: at(statement(2).entry, 0) <= at(statement(2).entry, capacity)
```

Like the owned-segmented-buffer order-weakening gap (fixed by the
`int32_le_transitive` standard theorem), the failure surfaced when commit
`e9460ff` rejected opaque outcome certificates. The
derivation here is wider than order weakening: the goal is a conjunction
mixing scalar bounds with a resource-count equality
(`count(pool_object(pool, _))`), and the certificate language has no simple
steps for splitting the outcome conjunction and certifying the count fact.
It is kept as a separate issue because the resource-count component likely
needs its own named rule, not just the scalar order theorem.

## Reproduction

```sh
target/debug/click verify examples/bounded-pool
```

The project is quarantined in `tests/examples.rs` until this is fixed.

## Acceptance criteria

- The unchanged bounded-pool project verifies and leaves quarantine.
- Focused regressions cover the outcome-conjunction split and the
  resource-count equality certificate separately.
- The fix does not restore opaque certificates.
