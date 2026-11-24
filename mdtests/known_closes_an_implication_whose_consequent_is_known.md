# `known` closes an implication whose consequent is an available fact

`A implies B` holds whatever `A` is once `B` holds, so `known` closes it with
one lookup of `B`, alone or as a conjunct. Without `B` available, it is not
closed.

```click
theorem consequent_known(a: int32, b: int32) {
    requires b > 0;
    ensures a > 3 implies b > 0 by { close(); }
}

theorem conjunct_consequent_known(a: int32, b: int32) {
    requires b > 0;
    requires a == 1;
    ensures (a > 3 implies b > 0) and a == 1 by { close(); }
}
```

```expect
pass
```
