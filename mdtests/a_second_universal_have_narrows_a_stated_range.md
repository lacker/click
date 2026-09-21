# A second universal `have` narrows a stated viewable range

Proving one universal fact must not take away a later quantified narrowing of
a range the contract states. The first `have` below is a triviality with no
memory in it at all; what it does do is put a universal proposition in the
context, whose bound variable identity is the one the second `have`'s lowering
also chose. `intro` therefore has to freshen the second universal's binder, and
that rename used to move the goal's byte extent from `((k + 1) - k) * 4` into
the folded `4`, which no re-lowering of the written range produces. The
narrowing then had nothing to match, and the refusal said the range had never
been stated.

```c filename=second_universal_have_narrows_a_stated_range.c
void walk(int32 *a, int32 *b, int32 n) {
    b[0] = 1;
}
```

```click
verifying "second_universal_have_narrows_a_stated_range.c";

void walk(int32 *a, int32 *b, int32 n) {
    views a[0..n];
    owns b[0..n];
    requires 1 <= n;
    requires n <= 1073741823;
} by {
    have forall (j: int32) {
        0 <= j and j < n implies 0 <= j
    } by {
        intro();
        intro();
        extract(0 <= j);
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < n implies viewable(a[k..k + 1])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        have k <= k + 1 by { arithmetic() using { 0 <= k; k < n; n <= 1073741823; } }
        have k + 1 <= n by { arithmetic() using { 0 <= k; k < n; n <= 1073741823; } }
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
