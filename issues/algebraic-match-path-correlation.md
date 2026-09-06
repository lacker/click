# Correlate repeated matches of one symbolic algebraic value

Lowering two pure calls that each eliminate the same symbolic algebraic value
currently enumerates their match arms independently. For a two-variant type,
the conjunction or disjunction of two observations therefore produces four
paths, including impossible cross-variant combinations, instead of the two
paths selected by the value's one constructor.

This was exposed while adding checked constructor rules. It is separate from
exhaustiveness: one match already enumerates every declared variant, and the
parser rejects missing or duplicate arms. The missing operation is preserving
one symbolic scrutinee's constructor refinement across repeated eliminations.

## Violated invariant

A typed algebraic term denotes one immutable constructor tree throughout a
proof. Every match of that term must use the same constructor choice. Lowering
must not treat repeated observations as independent nondeterministic values or
reject a true claim because their Cartesian product contains impossible paths.

## Intended regression

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

function tag(m: Maybe<int32>) -> int32 {
    match m {
        Maybe::None => 0,
        Maybe::Some(value) => 1,
    }
}

theorem tag_is_valid(m: Maybe<int32>) {
    ensures tag(m) == 0 or tag(m) == 1 by simp;
}
```

Today conclusion lowering reports that the kernel produced four paths rather
than one. Keep the original theorem unchanged when turning it into an mdtest.

## Acceptance criteria

- Repeated elimination of the same symbolic algebraic term reuses its exact
  constructor refinement and cannot create cross-variant paths.
- Correlation works through pure-function calls, direct `match` expressions,
  and aliases proved equal to the scrutinee.
- Distinct unconstrained algebraic values still enumerate independently.
- Work is proportional to the reachable correlated path set, not the full
  Cartesian product of repeated matches.
- Positive and negative mdtests and `scripts/check.sh` pass.

This is required for MVR because recursive tree models repeatedly observe the
same logical node and traversal value across invariant clauses.
