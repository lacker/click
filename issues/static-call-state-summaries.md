# Preserve static-local state through modular call summaries

Click can model a function-local scalar `static` and prove that repeated
writes within its owning function use one stable object. A modular caller
currently loses the relationship between a callee's static-dependent result
and the callee's post-call static state: two calls to a verified function can
leave the caller with an unconstrained result even when the callee contract
relates `result` to `old(static)` and the mutable footprint includes that
static object.

The violated invariant is that applying a verified call summary must preserve
all certified postconditions in the caller vocabulary, including relationships
between the returned value and persistent storage in the callee's mutable
footprint. The call's memory havoc may make the storage value symbolic, but it
must not discard the certified relation that the summary publishes.

Intended regression:

```c
int32 increment_twice() {
    static int32 calls = 5;
    calls = calls + 1;
    calls = calls + 1;
    return calls;
}

int32 call_twice() {
    int32 first;
    int32 second;
    first = increment_twice();
    second = increment_twice();
    return second;
}
```

With an owner contract stating `result == old(calls) + 2` and
`calls == old(calls) + 2`, the caller contract `ensures result == 9` should
verify. The regression must use opaque/modular calls, not body execution, so
it checks summary application rather than inlining.

Acceptance criteria:

- The caller-level regression above verifies through two modular calls.
- The first call's certified static update is available as the second call's
  entry fact.
- The result/static relationship remains sound when the static is included in
  the call's mutable footprint and memory havoc is applied.
- Existing call-summary, recursion, and static-local gates remain green.
