# Pure Integer existential elimination retains a checked symbolic witness

```click
theorem integer_exists_choose() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        obtain (candidate: Integer) { candidate == candidate }
        witness { k: candidate };
        assumption();
    }
}

theorem integer_exists_from_have() {
    ensures exists (z: Integer) { z == 0 } by {
        have exists (x: Integer) { x == 0 } by {
            witness { x: 0 };
            normalize();
        }
        obtain (candidate: Integer) { candidate == 0 }
        witness { z: candidate };
        assumption();
    }
}

theorem integer_exists_multiple_bindings() {
    requires exists (x: Integer, y: Integer) { x == y };
    ensures exists (a: Integer, b: Integer) { a == b } by {
        obtain (left: Integer, right: Integer) { left == right }
        witness { a: left };
        witness { b: right };
        assumption();
    }
}
```

```expect
pass
```
