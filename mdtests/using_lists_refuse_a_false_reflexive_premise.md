# A `using` list refuses a reflexive premise that is false

`n <= n` holds with no fact, so a `using` list accepts it
(`mdtests/using_lists_accept_premises_that_hold_without_facts.md`). Its
strict neighbour `n < n` is false for every `n`: the reflexive rule decides it
false, it is not an available fact, and the list refuses it. Accepting it would
let `strictly_below(n, n)` conclude the false `n < n`.

```c filename=using_lists_refuse_a_false_reflexive_premise.c
int32 probe(int32 n) {
    return 0;
}
```

```click
verifying "using_lists_refuse_a_false_reflexive_premise.c";

theorem strictly_below(lo: int32, n: int32) {
    requires lo < n;
    ensures lo < n by { assumption(); }
}

int32 probe(int32 n) {
    ensures result == 0;
} by {
    step();
    apply(strictly_below(n, n)) using {
        n < n;
    }
    simp();
}
```

```expect
fail: listed premise `n < n` is not an available fact
```
