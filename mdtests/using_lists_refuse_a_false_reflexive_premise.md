# A theorem application refuses a strict reflexive bound

```c filename=using_lists_refuse_a_false_reflexive_premise.c
int32 probe(int32 n) {
    return 0;
}
```

```click
verifying "using_lists_refuse_a_false_reflexive_premise.c";

theorem strictly_below(lo: int32, n: int32) {
    requires lo < n;
    ensures lo < n by close();
}

int32 probe(int32 n) {
    ensures result == 0;
} by {
    step();
    apply(strictly_below(n, n));
    close();
}
```

```expect
fail: has an unproved obligation: `n < n`
```
