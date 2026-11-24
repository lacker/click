# Pure sequence membership retains its operands

```click
theorem membership_with_concat(a: int32, b: int32) {
    ensures forall (unused: Integer) {
        a in [] ++ ([b] ++ [a])
    } by { intro(); close(); }
}

theorem singleton(a: int32) {
    ensures forall (unused: Integer) { a in [a] }
    by { intro(); close(); }
}

theorem empty(a: int32) {
    ensures forall (unused: Integer) { not (a in []) }
    by { intro(); close(); }
}

theorem membership_case_split(a: int32) {
    requires a in [1] ++ [2];
    ensures 0 < a by {
        cases { a == 1 => { close(); } a == 2 => { close(); } }
    }
}

theorem nonmembership_projects_elements(a: int32, b: int32, c: int32) {
    requires not (a in [b, c]);
    ensures a != b by close();
}
theorem rewrite_membership(a: int32, b: int32) {
    requires a == b;
    ensures a in [] ++ [b] by { rewrite(a, b); close(); }
}

theorem known_disjunction_proves_membership(a: int32, b: int32, c: int32) {
    requires a == b or a == c;
    ensures a in [b, c] by close();
}
```

```expect
pass
```
