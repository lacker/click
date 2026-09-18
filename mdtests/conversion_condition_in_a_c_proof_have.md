# a conversion condition inside a C proof's `have` names the same things

The same refusal reaches a `have` lowered against a C function's symbolic state.
There the premise set is the proof's own facts, so the message lists those rather
than a theorem's `requires`, and the range premise the `views` clause put in
scope is named as the one that was consulted and did not suffice.

```c filename=conversion_condition_in_a_c_proof_have.c
int32 last_of_view(int32 *p, int32 lo, int32 hi) {
    return hi;
}
```

```click
verifying "conversion_condition_in_a_c_proof_have.c";

int32 last_of_view(int32 *p, int32 lo, int32 hi) {
    requires 0 <= lo;
    requires lo < hi;
    views p[lo..hi];
    ensures result == hi by {
        have to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
        step();
        simp();
    }
}
```

```expect
fail: not established: the 4 bytes at `p[hi - 1]` must be loadable
```
