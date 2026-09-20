# a fact about an array survives a separate object's allocation

`malloc` records a request with no address yet, and the successful arm resolves
it into a fresh object. A fresh heap block is an object the kernel proves is not
the array the caller passed, and the request itself records nothing any read
consults, so nothing `icount` can observe through `a` changes across the
declaration, the request or the allocation.

The release of that object is separate too, by the same rule, but a fact cannot
be carried to a point after it here: the `branch` continuation this proof
returns to is reached by a transition that records no edge, so the recorded
execution stops connecting the two points one step later. That is a gap in what
the execution records, not in the rule, and it fails closed.

```c filename=array_fact_survives_a_separate_allocation.c
int32 scratch(int32 a[], int32 n) {
    int32* fresh;
    fresh = malloc(4);
    if (fresh == 0) {
        return 0;
    }
    free(fresh);
    return 0;
}
```

```click
verifying "array_fact_survives_a_separate_allocation.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

int32 scratch(int32 a[], int32 n) {
    requires 0 < n;
    views a[0..n];
} by {
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    step();
    step();
    branch {
        then {
            execute();
            simp();
        }
        else {
        }
    }
    have icount(a, 0, 0) == 0 by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
