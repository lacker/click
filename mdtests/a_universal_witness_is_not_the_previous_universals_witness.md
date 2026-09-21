# a universal witness is not the previous universal's witness

Two universal `have`s in one proof lower their binders to the same identity,
so the second one's `intro` has to freshen. Freshening has to reach an
identity the first introduction did not already use, or the antecedent the
first `intro` put in scope is an antecedent about the second's witness and the
second universal is provable over a range it was never quantified with.

The first universal below bounds its variable by `5`. The second is quantified
over every `int32` with no bound at all, and its body is false for anything
`5` or larger, so it must not be provable from anything the first left behind.

```c filename=universal_witness_is_fresh_each_time.c
int32 walk(int32 n) {
    return n;
}
```

```click
verifying "universal_witness_is_fresh_each_time.c";

int32 walk(int32 n) {
    requires 1 <= n;
    ensures result == n;
} by {
    have forall (j: int32) {
        0 <= j and j < 5 implies 0 <= j
    } by {
        intro();
        intro();
        extract(0 <= j);
        assumption();
    }
    have forall (k: int32) {
        0 <= k implies k < 5
    } by {
        intro();
        intro();
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
