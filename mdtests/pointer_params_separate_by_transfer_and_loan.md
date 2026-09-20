# transferring one pointer parameter and lending the other separates them

The C of `pointer_params_may_alias_without_separate.md`, with the contract
saying what that one deliberately leaves unsaid. `dst` is transferred and
`src` is lent, and a contract's transferred and borrowed clauses denote
disjoint memory (`docs/internals/resource-tracker.md`, "The entry
partition"), so the write through `dst` cannot be the write that changed
`src[0]`. No `separate(...)` clause is needed.

The caller owes nothing extra for this: it is the call-site planner that
discharges it, by reserving every owned requirement out of the caller's
residual before it plans a view. A caller passing one range to both clauses
is refused — `a_caller_cannot_lend_and_transfer_one_range.md`.

```c filename=pointer_params_separate_by_transfer_and_loan.c
int32 clobber_dst(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
verifying "pointer_params_separate_by_transfer_and_loan.c";

int32 clobber_dst(int32* dst, int32* src) {
    consumes dst[0..1];
    views src[0..1];

    ensures source_unchanged: src[0] == old(src[0]);
} by { execute(); simp(); }
```

```expect
pass
```
