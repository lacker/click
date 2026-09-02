# a finite universal instantiates the hull of its guards

Both conjuncts are guarded implications, so the universal is vacuous outside
`0..10` and is proved by checking every `k` in that hull, including the
`3..10` where the first guard is false.

```c filename=c_finite_forall_hull_of_two_guards.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "c_finite_forall_hull_of_two_guards.c";

int32 identity(int32 x) {
    ensures forall (k: int32) {
        ((0 <= k and k < 3) implies 0 <= k) and ((0 <= k and k < 10) implies k < 10)
    };
} by {
    execute();
    simp();
}
```

```expect
pass
```
