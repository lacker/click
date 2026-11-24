# A theorem application names the missing instantiated bound

```c filename=apply_using_names_a_false_constant_premise.c
int32 probe(int32 n) {
    return 0;
}
```

```click
verifying "apply_using_names_a_false_constant_premise.c";

theorem start_below(lo: int32, n: int32) {
    requires 0 <= lo;
    requires lo <= n;
    ensures 0 <= n by close();
}

int32 probe(int32 n) {
    requires 0 <= n;
    ensures result == 0;
} by {
    step();
    apply(start_below(1, n));
    close();
}
```

```expect
fail: has an unproved obligation: `1 <= n`
```
