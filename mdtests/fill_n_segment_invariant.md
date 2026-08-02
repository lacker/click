# fill_n proves a quantified written segment

This checks that a memory-changing symbolic loop can use a quantified loop
invariant to describe the segment that has already been written.

```c filename=fill_n_segment_invariant.c
int32 fill_n_segment_invariant(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "fill_n_segment_invariant.c";

int32 fill_n_segment_invariant(int32 p[], int32 n) {
    requires n >= 0 and n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    for loop(0) {
        invariant i >= 0 and i <= n;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == k
        };
        initialize by auto;
        preserve by {
            step();
            step();
            have i == at(loop(0).entry, i) + 1 by simp;
            simp();
        }
    }
    ensures returns_n: result == n;
    ensures filled_segment: forall (k: int32) {
        0 <= k and k < n implies p[k] == k
    };
} by {
    step() using {
        n >= 0;
        n <= 2147483647;
        loadable(p[0..n]);
    }
    step() using {
        n >= 0;
        n <= 2147483647;
        loadable(old(p[0..n]));
    }
    have i >= 0 by {
        normalize();
    }
    have i <= n by {
        derive using {
            n >= 0;
        }
    }
    have forall (k: int32) { 0 <= k and k < i implies p[k] == k } by {
        normalize();
    }
    summarize(loop(0)) using {
        n >= 0 and n <= 2147483647;
        loadable(old(p[0..n]));
        i >= 0;
        i <= n;
        forall (k: int32) { 0 <= k and k < i implies p[k] == k };
    }
    step() using {
        n >= 0;
        n <= 2147483647;
        loadable(old(p[0..n]));
        at(loop(0).exit, i) >= at(loop(0).exit, 0);
        at(loop(0).exit, i) <= at(loop(0).exit, n);
        not i < n;
    }
    have result == n by {
        derive using {
            at(statement(5).entry, n) >= at(statement(5).entry, 0);
            at(statement(5).entry, n) <= at(statement(5).entry, 2147483647);
            at(statement(5).entry, loadable(old(p[0..n])));
            at(statement(5).entry, i) >= at(statement(5).entry, 0);
            at(statement(5).entry, i) <= at(statement(5).entry, n);
            not at(statement(5).entry, i) < at(statement(5).entry, n);
            at(statement(2).entry, n) >= at(statement(2).entry, 0) and at(statement(2).entry, n) <= at(statement(2).entry, 2147483647);
            at(statement(2).entry, i) >= at(statement(2).entry, 0);
            at(statement(2).entry, i) <= at(statement(2).entry, n);
            forall (k: int32) { at(statement(2).entry, 0) <= at(statement(2).entry, k) and at(statement(2).entry, k) < at(statement(2).entry, i) implies at(statement(2).entry, p[k]) == at(statement(2).entry, k) };
            at(loop(0).exit, i) >= at(loop(0).exit, 0) and at(loop(0).exit, i) <= at(loop(0).exit, n);
        }
    }
    have forall (k: int32) { 0 <= k and k < n implies p[k] == k } by {
        derive using {
            result == n;
            forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, p[k]) == at(loop(0).exit, k) };
        }
    }
    assumption();
    assumption();
}
```

```expect
pass
```
