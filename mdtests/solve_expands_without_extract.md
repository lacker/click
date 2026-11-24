# Solver logical projections have explicit proofs without extract

```click
spec enum Box { Item(int32), }

theorem excluded_middle(make: Bool) {
    ensures make or not make by close();
}

theorem conjunction_projection(x: int32, y: int32, z: int32) {
    requires x > 0 and y > 0 and z > 0;
    ensures y > 0 and z > 0 by close();
}

theorem implication_application(x: int32, y: int32) {
    requires x > 0;
    requires x > 0 implies y > 0;
    ensures y > 0 by close();
}

theorem implication_partial_chain(x: int32, y: int32, z: int32) {
    requires x > 0;
    requires x > 0 implies y > 0 implies z > 0;
    ensures y > 0 implies z > 0 by close();
}

theorem implication_conjunct(x: int32, y: int32, z: int32) {
    requires x > 0;
    requires x > 0 implies (y > 0 and z > 0);
    ensures z > 0 by close();
}

theorem constructor_projection(x: int32, y: int32) {
    requires Box::Item(x) == Box::Item(y);
    ensures x == y by close();
}

theorem disjunction_projection(x: int32, y: int32) {
    requires (x > 0 and y == 1) or (x > 0 and y == 2);
    ensures x > 0 by close();
}

theorem nested_disjunction_projection(x: int32, y: int32) {
    requires (x > 0 and y == 1) or ((x > 0 and y == 2) or (x > 0 and y == 3));
    ensures x > 0 by close();
}

theorem selected_implication(x: int32, y: int32) {
    requires x > 0;
    requires x > 0 implies y > 0;
    ensures y > 0 by close() using { x > 0; x > 0 implies y > 0; };
}

theorem quantified_conclusion(flag: int32) {
    requires flag != 0;
    requires flag != 0 implies exists (caller_path: Nat) { caller_path == Nat::Zero };
    ensures exists (path: Nat) { path == Nat::Zero } by close();
}
```

```expect
pass
```
