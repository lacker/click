# a second guard widens the range a finite universal must cover

The first implication is vacuous outside `0..3`, the second outside `0..10`.
The universal is therefore vacuous only outside `0..10`, and `k < 5` fails
at `k = 5`. Instantiating the narrower guard alone must not prove it.

```c filename=c_finite_forall_rejects_wider_second_guard.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "c_finite_forall_rejects_wider_second_guard.c";

int32 identity(int32 x) {
    ensures bad: forall (k: int32) {
        ((0 <= k and k < 3) implies 0 <= k) and ((0 <= k and k < 10) implies k < 5)
    };
} by {
    execute();
    simp();
}
```

```expect
fail: identity.bad
```
