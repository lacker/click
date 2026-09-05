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

theorem sequence_concat_associative(a: int32, b: int32, c: int32) {
    ensures [a] ++ [b] ++ [c] == [a] ++ ([b] ++ [c]) by simp;
}

theorem sequence_literal_and_concat_have_the_same_contents(a: int32, b: int32, c: int32) {
    ensures [a, b] ++ [c] == [a] ++ [b, c] by simp;
}

theorem sequence_length_distinguishes_multiplicity() {
    ensures [0] != [0, 0] by simp;
}

theorem sequence_order_is_observable() {
    ensures [0, 1] != [1, 0] by simp;
}

theorem singleton_contains_its_element(a: int32) {
    ensures a in [a] by simp;
}

theorem membership_crosses_concatenation(a: int32, b: int32) {
    ensures a in [b] ++ [a] by simp;
}

theorem equality_can_establish_membership(a: int32, b: int32) {
    requires a == b;
    ensures a in [b, 0] by simp;
}

theorem pointer_membership_preserves_identity(a: int32*, b: int32*) {
    ensures a in [b, a] by simp;
}

theorem empty_sequence_has_no_members(a: int32) {
    ensures not (a in []) by simp;
}

theorem absent_constant_is_not_a_member() {
    ensures not (2 in [0, 1]) by simp;
}
```

```expect
pass
```
