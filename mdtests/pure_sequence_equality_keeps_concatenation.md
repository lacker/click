# Pure int32 sequence comparisons keep concatenation

```click
theorem keeps_concatenation(a: int32, b: int32) {
    ensures forall (unused: Integer) {
        [] ++ [a] ++ [b] == [a, b] ++ []
    } by { intro(); close(); }
}

theorem keeps_rewritten_concatenation(a: int32, b: int32) {
    requires a == b;
    ensures forall (unused: Integer) {
        [a] ++ [] == [b]
    } by { intro(); rewrite(a, b); close(); }
}

theorem sequence_premise_exposes_elements(a: int32, b: int32, c: int32, d: int32) {
    requires [a] ++ [b] == [c, d];
    ensures b == d by close();
}

theorem known_checks_each_element(a: int32, b: int32, c: int32, d: int32) {
    requires a == c;
    requires b == d;
    ensures [a, b] == [c] ++ [d] by close();
}

theorem all_checks_each_element(a: int32, b: int32, c: int32, d: int32) {
    requires a == c;
    requires b == d;
    ensures [a, b] == [c] ++ [d] by {
        all { a == c => { close(); } b == d => { close(); } }
    }
}

theorem wrong_length(a: int32) {
    ensures [a] ++ [] != [a, a] by close();
}

theorem wrong_element(a: int32, b: int32) {
    requires a != b;
    ensures [a] ++ [] != [b] by close();
}
```

```expect
pass
```
