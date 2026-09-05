# finite sequence literals and concatenation

Specification sequences preserve exact order and multiplicity. This first
slice checks literal construction, empty identity, and persistent
concatenation through ordinary kernel proofs.

```click
theorem sequence_literal_reflexive(a: int32, b: int32) {
    ensures [a, b] == [a, b] by simp;
}

theorem sequence_empty_left_identity(a: int32) {
    ensures [] ++ [a] == [a] by simp;
}

theorem sequence_empty_right_identity(a: int32) {
    ensures [a] ++ [] == [a] by simp;
}

theorem sequence_concat_reflexive(a: int32, b: int32, c: int32) {
    ensures [a] ++ [b, c] == [a] ++ [b, c] by simp;
}

theorem sequence_length_distinguishes_multiplicity() {
    ensures [0] != [0, 0] by simp;
}

theorem sequence_order_is_observable() {
    ensures [0, 1] != [1, 0] by simp;
}
```

```expect
pass
```
