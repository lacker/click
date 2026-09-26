# Every `using` list accepts a premise that holds without facts

A listed premise that lowers to the ground constant it asserts (`0 <= 0`), or
to a comparison of a term with itself (`n <= n`), holds with no fact behind
it. The listed-premise check every `using` list shares accepts both, so
the same premise is accepted by `unfold ... using`, `apply ... using`,
`instantiate ... using` and `arithmetic() using` alike, and a proof does not
need a `have 0 <= 0` or `have n <= n` first.

The kernel's condition decision answers the same reflexive comparisons, so a
call whose precondition instantiates to `n <= n` needs no fact either. The
false neighbours, `n < n` and `n != n`, are refused:
`mdtests/using_lists_refuse_a_false_reflexive_premise.md`.

```c filename=using_lists_accept_premises_that_hold_without_facts.c
void empty_prefix(int32 a[], int32 n) {
    int32 i;
    i = 0;
}

void empty_suffix(int32 a[], int32 n) {
    int32 i;
    i = 0;
}

int32 probe(int32 n) {
    return 0;
}

int32 span(int32 lo, int32 hi) {
    return hi - lo;
}

int32 call_span(int32 n) {
    return span(n, n);
}
```

```click
verifying "using_lists_accept_premises_that_hold_without_facts.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

theorem start_below(lo: int32, n: int32) {
    requires 0 <= lo;
    requires lo <= n;
    ensures 0 <= n by { simp(); }
}

theorem last_cell(a: int32[], n: int32) {
    requires forall (k: int32) { 0 <= k and k <= n implies a[k] == 0 };
    requires 0 <= n;
    views a[0..n + 1];
    requires n < 100;
    ensures a[n] == 0 by {
        instantiate(forall (k: int32) { 0 <= k and k <= n implies a[k] == 0 }, n) using {
            0 <= n;
            n <= n;
        }
        assumption();
    }
}

theorem listed_arithmetic(n: int32) {
    requires 0 <= n;
    ensures 0 <= n by {
        arithmetic() using { 0 <= n; n <= n; 0 <= 0; }
    }
}

void empty_prefix(int32 a[], int32 n) {
    requires 0 < n;
    views a[0..n];
} by {
    step();
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    execute();
    simp();
}

void empty_suffix(int32 a[], int32 n) {
    requires 0 < n;
    views a[0..n];
} by {
    step();
    have icount(a, n, n) == 0 by {
        unfold(icount(a, n, n)) using { n <= n; }
        normalize();
    }
    execute();
    simp();
}

int32 probe(int32 n) {
    requires 0 <= n;
    ensures result == 0;
} by {
    step();
    apply(start_below(n, n)) using {
        0 <= n;
        n <= n;
    }
    simp();
}

int32 span(int32 lo, int32 hi) {
    requires lo <= hi;
    requires 0 <= lo;
    ensures result == hi - lo by auto;
}

int32 call_span(int32 n) {
    requires 0 <= n;
    ensures result == 0 by auto;
}
```

```expect
pass
```
