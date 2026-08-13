# Owned-segmented-buffer rides its project deadline under load

`examples/owned-segmented-buffer` verifies in about 22s warm debug CPU
against the default 30s project deadline. Under machine load it can cross
the deadline and fail, which makes the suite's green load-sensitive (observed
during 2026-08-11 reliability work, on pristine master, unrelated to the
changes then in flight).

Same shape as the binary-tree aggregate-cost issue: no individual tactic is
over budget (all are far inside the deterministic simple work budget), so the
cost lives in aggregate certification/verifier-core work.

## 2026-08-12 narrow attribution

A complete structured profile under load took 28.147s and isolated nearly all
of the instability to `owned_segmented_buffer_pipeline`:

```text
pipeline total                                21.550s
independent kernel certification                6.797s
contract symbolic execution                     6.608s
  contract body symbolic execution              6.569s
whole-contract certificate replay               0.913s
```

The other five functions together account for about 6.4s. Unlike
owned-string, derived entry facts are not the problem here (300ms total): the
pipeline body is genuinely executed twice, once for proof certification and
once for independent opaque-contract certification. This is now the primary
reduced target. Any deduplication must preserve the independent kernel
boundary; the profile rules out quantified-entry setup and resource
representation as the dominant cause.

## Acceptance criteria

- Warm ordinary verification completes with comfortable margin against the
  30s deadline (or the aggregate cost is attributed and reduced per the
  binary-tree/owned-string performance issues).
- No budget or deadline is raised, and no claim or C source is weakened.
