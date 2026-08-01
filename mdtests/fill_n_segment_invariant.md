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
        invariant forall (int32 k) {
            0 <= k and k < i implies p[k] == k
        };
        initialize by auto;
        preserve by {
            execute_step();
            execute_step();
            have i == at(loop(0).entry, i) + 1 by {
                simp();
            }
            simp();
        }
    }
    ensures returns_n: result == n;
    ensures filled_segment: forall (int32 k) {
        0 <= k and k < n implies p[k] == k
    };
} by {
    step using {
        fact n >= 0;
        fact n <= 2147483647;
        fact loadable(p[0..n]);
    }
    step using {
        fact n >= 0;
        fact n <= 2147483647;
        fact loadable(old(p[0..n]));
    }
    have i >= 0 by {
        normalize();
    }
    have i <= n by {
        derive(i <= n) using {
            fact n >= 0;
        }
    }
    have forall (int32 k) { 0 <= k and k < i implies p[k] == k } by {
        normalize();
    }
    apply_loop_summary(loop(0)) using {
        fact n >= 0 and n <= 2147483647;
        fact loadable(old(p[0..n]));
        fact i >= 0;
        fact i <= n;
        fact forall (int32 k) { 0 <= k and k < i implies p[k] == k };
    }
    step using {
        fact n >= 0;
        fact n <= 2147483647;
        fact loadable(old(p[0..n]));
        fact at(loop(0).exit, i) >= at(loop(0).exit, 0);
        fact at(loop(0).exit, i) <= at(loop(0).exit, n);
        fact not i < n;
    }
    have result == n by {
        derive(result == n) using {
            fact at(statement(5).entry, n) >= at(statement(5).entry, 0);
            fact at(statement(5).entry, n) <= at(statement(5).entry, 2147483647);
            fact at(statement(5).entry, loadable(old(p[0..n])));
            fact at(statement(5).entry, i) >= at(statement(5).entry, 0);
            fact at(statement(5).entry, i) <= at(statement(5).entry, n);
            fact not at(statement(5).entry, i) < at(statement(5).entry, n);
            fact at(statement(2).entry, n) >= at(statement(2).entry, 0) and at(statement(2).entry, n) <= at(statement(2).entry, 2147483647);
            fact at(statement(2).entry, i) >= at(statement(2).entry, 0);
            fact at(statement(2).entry, i) <= at(statement(2).entry, n);
            fact forall (int32 k) { at(statement(2).entry, 0) <= at(statement(2).entry, k) and at(statement(2).entry, k) < at(statement(2).entry, i) implies at(statement(2).entry, p[k]) == at(statement(2).entry, k) };
            fact at(loop(0).exit, i) >= at(loop(0).exit, 0) and at(loop(0).exit, i) <= at(loop(0).exit, n);
        }
    }
    have forall (int32 k) { 0 <= k and k < n implies p[k] == k } by {
        derive(forall (int32 k) { 0 <= k and k < n implies p[k] == k }) using {
            fact result == n;
            fact forall (int32 k) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, p[k]) == at(loop(0).exit, k) };
        }
    }
    assumption();
    assumption();
}
```

```expect
pass
```
