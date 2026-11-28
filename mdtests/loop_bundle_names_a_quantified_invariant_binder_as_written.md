# A quantified bundle member names its binder as the invariant wrote it

The back edge of
[`loop_initialize_narrows_a_held_range_under_a_universal.md`](loop_initialize_narrows_a_held_range_under_a_universal.md)
owes the span bound of `viewable(a[0..k])` for every `k` the quantified
invariant covers, as its own bundle member
`forall (k: int32) { 0 <= k and k <= n implies (k as uint32) <= 1073741823u32 }`.
The closer synthesizes a source form for this kernel-generated member.
When synthesis gave the binder a fresh name, a proof that focused the
member with `both` and introduced it still had no binding for `k`.
The binder now takes the name the invariant gave it, so the explicit
proof below can write `have 0 <= k;`.

```c filename=loop_bundle_names_a_quantified_invariant_binder_as_written.c
int32 count_up(int32 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_bundle_names_a_quantified_invariant_binder_as_written.c";

int32 count_up(int32 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k <= n;
                        close();
                    }
                }
            }
            close();
        }
        maintain by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k <= n;
                        close();
                    }
                }
            }
        }
    }
}
```

```expect
pass
```
