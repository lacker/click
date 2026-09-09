# By-value struct postconditions must not escape the callee copy

**Severity: critical.** A callee can be certified against its private copy of a
by-value struct and the resulting postcondition can then be instantiated on the
caller's object. This creates contradictory caller facts and makes arbitrary
claims verify.

**Violated invariant.** A by-value parameter is a callee-local object. Its
post-state is not observable by the caller, so an `ensures` proposition may not
read that parameter's current fields after the body modifies its copy.

**Regression** (`mdtests/by_value_struct_param_ensures_rejected.md`):

```c
struct pair {
    int32 first;
    int32 second;
};

int32 bump(struct pair value) {
    value.first = 5;
    return value.first;
}

int32 call_bump() {
    struct pair original;
    int32 r;
    original.first = 4;
    original.second = 0;
    r = bump(original);
    return original.first;
}
```

```click
verifying "t.c";

int32 bump(struct pair value) {
    ensures value.first == 5;
} by {
    execute();
    simp();
}

int32 call_bump() {
    ensures result == 999;
} by {
    execute();
    simp();
}
```

`call_bump` returns 4. Before the fix, the callee's `value.first == 5` was
applied to `original.first`, so the caller had both `original.first == 4` and
`original.first == 5` and could prove `result == 999`.

**Acceptance criteria.**

- The regression is rejected because `bump` writes its private aggregate copy
  while its postcondition reads that copy in the current state.
- A postcondition that reads only `old(value.first)` remains accepted, covered
  by `mdtests/by_value_struct_param_old_ensures.md`.
- A postcondition over `value` remains accepted when the body does not modify
  the by-value copy, including the existing `choose_packet` and `sum_packet`
  contracts.
- `mdtests/struct_by_value_scalar_copy.md` and the rest of the by-value family
  continue to pass.

The check compares each aggregate parameter's entry and exit storage after
body execution. A changed or havocked copy is private to the callee and cannot
be used as a current-state caller fact; entry-state reads under `old(...)` are
still valid.
