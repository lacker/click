# sorted is a general range predicate

This checks that Click can define and explicitly unfold a general quantified
`sorted(p, n)` predicate. The predicate is still opaque unless the proof script
uses `unfold(sorted)`.

```c filename=sorted_predicate.c
int32 sorted_predicate(int32 p[], int32 n) {
    return 0;
}
```

```click
verifying "sorted_predicate.c";

predicate sorted(int32 p[], int32 n) {
    forall (int32 i) {
        forall (int32 j) {
            0 <= i and 0 <= j and i < j and j < n implies p[i] <= p[j]
        }
    }
}

int32 sorted_predicate(int32 p[], int32 n) {
    requires n >= 0;
    requires loadable(p[0..n]);
    requires sorted(p, n);
    ensures still_sorted: sorted(p, n) by {
        execute();
        unfold(sorted);
        simp();
    }
}
```

```expect
pass
```
