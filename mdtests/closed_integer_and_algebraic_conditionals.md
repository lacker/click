# Closed Integer and algebraic comparisons keep the conditional operand

```click
spec enum Choice { Left, Right }

theorem integer_order(x: Integer, y: Integer) {
    ensures forall (unused: Integer) {
        ((if 1 < 2 { x } else { y }) : Integer) <= x
    } by { intro(); close(); }
}

theorem integer_equality(x: Integer, y: Integer) {
    ensures forall (unused: Integer) {
        ((if false { x } else { y }) : Integer) == y
    } by { intro(); close(); }
}

theorem algebraic_equality() {
    ensures forall (unused: Integer) {
        (if 1 == 2 { Choice::Left } else { Choice::Right }) == Choice::Right
    } by { intro(); close(); }
}

theorem algebraic_disequality() {
    ensures (if 1 < 2 { Choice::Left } else { Choice::Right }) != Choice::Right by close();
}

theorem algebraic_argument(a: Choice, b: Choice) {
    ensures forall (unused: Integer) {
        (if true { a } else { b }) == a
    } by { intro(); close(); }
}

theorem dead_arm_domain(x: Integer) {
    ensures ((if true { x } else { truncating_quotient(1, 0) }) : Integer) == x by close();
}

theorem uses_integer_bound(x: Integer, y: Integer) {
    requires ((if true { x } else { y }) : Integer) <= 5;
    ensures x <= 5 by close();
}

theorem checks_integer_bound(x: Integer, y: Integer) {
    requires x <= 5;
    ensures ((if true { x } else { y }) : Integer) <= 5 by close();
}

theorem uses_algebraic_equality(a: Choice, b: Choice) {
    requires (if true { a } else { b }) == Choice::Left;
    ensures a == Choice::Left by close();
}

theorem checks_algebraic_equality(a: Choice, b: Choice) {
    requires a == Choice::Left;
    ensures (if true { a } else { b }) == Choice::Left by close();
}
```

```expect
pass
```
