# `instantiate using` names the listed premise it could not find

The second listed premise, `k < 7`, is not a fact on this path: the contract
bounds `k` by `n`, not by `7`. The refusal names that premise by its position
and in the proof's own spelling, rather than as a kernel term dump.

```c filename=instantiate_using_names_the_unavailable_premise.c
int32 pick(int32 a[], int32 n, int32 k) {
    return a[k];
}
```

```click
verifying "instantiate_using_names_the_unavailable_premise.c";

int32 pick(int32 a[], int32 n, int32 k) {
    requires 0 <= k and k < n;
    requires viewable(a[0..n]);
    views a[0..n];
    requires forall (j: int32) { 0 <= j and j < n implies a[j] >= 0 };
    ensures result >= 0;
} by {
    have a[k] >= 0 by {
        instantiate(forall (j: int32) { 0 <= j and j < n implies a[j] >= 0 }, k) using {
            0 <= k;
            k < 7;
        }
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: `instantiate using` premise 2 `k < 7` is not an available exact fact
```
