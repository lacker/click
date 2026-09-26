# A written `viewable` range states its extent in the signed spelling

`views a[0..n]` over `int32` carries the range's extent as two facts a proof
can write, `0 <= n` and `n <= 1073741823`, beside the endpoint form memory
reasoning reads, whose `fits` half is an unsigned comparison. A written
`requires viewable(a[0..n])` states the same range, and it used to carry only
the endpoint form, so `ensures result <= 1073741823 by auto` held under
`views` and failed under `viewable`. Both clauses now carry the same guards in
the same spellings, at function entry and wherever a caller owes them, and a
call's `ensures viewable(a[0..result])` gives the caller `result <= 1073741823`
the same way.

```c filename=a_written_viewable_range_states_its_extent_in_the_signed_spelling.c
int32 count_viewable(int32 *a, int32 n) {
    return n;
}

int32 count_views(int32 *a, int32 n) {
    return n;
}

int32 caller(int32 *a, int32 n) {
    int32 k = count_viewable(a, n);
    return k;
}

int32 prefix(int32 *a, int32 n) {
    return n;
}

int32 prefix_caller(int32 *a, int32 n) {
    int32 k = prefix(a, n);
    return k;
}
```

```click
verifying "a_written_viewable_range_states_its_extent_in_the_signed_spelling.c";

int32 count_viewable(int32 *a, int32 n) {
    requires viewable(a[0..n]);
    ensures 0 <= result by auto;
    ensures result <= 1073741823 by auto;
}

int32 count_views(int32 *a, int32 n) {
    views a[0..n];
    ensures 0 <= result by auto;
    ensures result <= 1073741823 by auto;
}

int32 caller(int32 *a, int32 n) {
    requires viewable(a[0..n]);
    ensures result <= 1073741823 by auto;
}

int32 prefix(int32 *a, int32 n) {
    requires viewable(a[0..n]);
    ensures viewable(a[0..result]) by auto;
}

int32 prefix_caller(int32 *a, int32 n) {
    requires viewable(a[0..n]);
    ensures result <= 1073741823 by auto;
}
```

```expect
pass
```
