# A claim true in only one alias case of a load is refused

The negative of
[`a_load_that_may_read_an_earlier_store_splits_into_its_cases.md`](a_load_that_may_read_an_earlier_store_splits_into_its_cases.md).
`r = g[0]` reads the `7` that `g[u] = 7` stored only when `u == 0`; for any
other `u` it reads the entry value. `execute()` splits the load into those two
cases and continues each, and the claim `result == 8` holds only in the first.
The refusal is the ordinary unclosed goal of the other case, where the result
is the entry value of `g[0]` plus one. Its proof context names that case,
`0 == u is false`, on a line of its own: the condition shares no term with the
goal, while the unrelated `requires u < 4` stays out.

```c filename=a_claim_true_in_one_alias_case_is_refused.c
int32 g[4];

int32 planned(int32 u) {
    int32 r;
    g[u] = 7;
    r = g[0];
    r = r + 1;
    return r;
}
```

```click
verifying "a_claim_true_in_one_alias_case_is_refused.c";

int32 planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    requires g[0] < 100;
    owns g[0..4];
    ensures result == 8;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 8` failed for `planned.ensures_0` path 1: unclosed goal: result == 8; left side evaluated to (load(&g) + 1), right side evaluated to 8
proof context for the goal:
  case: [0 != u]
  pure facts: [int32 <(load A=read<Bits32>(snapshot#1, pointer=value#1), 100) is true]
```
