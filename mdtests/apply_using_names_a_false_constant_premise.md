# `apply using` names a listed premise that is constantly false

`1 <= 0` lowers to the ground constant `false`. It is not evidence for
anything, so the list refuses it, and the refusal names the listed premise in
the proof's own spelling rather than as an anonymous constant condition. The
constantly-true neighbour is `mdtests/apply_using_accepts_a_constant_true_premise.md`.

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
    ensures 0 <= n by { simp(); }
}

int32 probe(int32 n) {
    requires 0 <= n;
    ensures result == 0;
} by {
    step();
    apply(start_below(1, n)) using {
        1 <= 0;
        1 <= n;
    }
    simp();
}
```

```expect
fail: listed premise `1 <= 0` (it is false at this instance) is not an available fact: missing pure fact: constant condition `false` is true
```
