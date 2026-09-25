# Logical conversion does not require a viewable cell

A logical read has a value even without a proved viewable extent. Its
reflexive equality needs no validity premise; actual C reads remain checked.

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
pass
```
