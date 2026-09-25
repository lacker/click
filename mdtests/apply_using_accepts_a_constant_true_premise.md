# `apply using` accepts a premise that is constantly true at the instance

Applying a theorem at `lo = 0` owes `0 <= lo`, which at that instance is
`0 <= 0`. Naming it in the `using` list lowers it to the ground constant
`true`, and the list used to refuse it without saying which entry it meant:

```text
`apply using` requires an exact premise: missing pure fact: constant condition
is true
```

A listed premise whose lowering is the constant it asserts needs no fact; the
requirement side already discharges the same instance without one. A premise
that is constantly false still refuses, and names itself:
`mdtests/apply_using_names_a_false_constant_premise.md`.

```c filename=apply_using_accepts_a_constant_true_premise.c
int32 probe(int32 n) {
    return 0;
}
```

```click
verifying "apply_using_accepts_a_constant_true_premise.c";

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
    apply(start_below(0, n)) using {
        0 <= 0;
        0 <= n;
    }
    simp();
}
```

```expect
pass
```
