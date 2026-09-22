# An ordinary separation clause needs no extent text

A separation premise includes the validity of the ranges it names. Its
endpoints can remain symbolic: the function assumes the bounds along with
separation, so the contract does not have to repeat them. A caller must prove
both separation and the bounds. The complementary goal and call regressions
are in `separation_extent_unbounded_goal_rejected.md` and
`separation_extent_call_rejected.md`.

```c filename=an_ordinary_separation_clause_needs_no_extent_text.c
int32 ordinary_separation(int32 a[], int32 b[], int32 n) {
    return b[0];
}
```

```click
verifying "an_ordinary_separation_clause_needs_no_extent_text.c";

int32 ordinary_separation(int32 a[], int32 b[], int32 n) {
    requires 0 <= n;
    requires separate(memory(a[0..n]), memory(b[0..1]));
    owns b[0..1];

    ensures result == b[0] by auto;
}
```

```expect
pass
```
