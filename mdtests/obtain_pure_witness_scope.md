# Obtained witnesses remain in scope for later proof steps

```click
theorem obtained_int32(x: int32) {
    requires exists (k: int32) { k > x };
    requires forall (j: int32) { j > x implies j > 1000 };
    ensures exists (z: int32) { z > 1000 } by {
        obtain (k: int32) { k > x }
        have k > x by assumption();
        have forall (k: int32) { k == k } by { intro(); normalize(); }
        instantiate(forall (j: int32) { j > x implies j > 1000 }, k)
            using { k > x; }
        have k > 1000;
        witness { z: k };
        assumption();
    }
}

theorem obtained_uint32(x: uint32) {
    requires exists (k: uint32) { k == x };
    ensures exists (z: uint32) { z == x } by {
        obtain (k: uint32) { k == x }
        have k == x by assumption();
        witness { z: k };
        assumption();
    }
}

theorem obtained_int64(x: int64) {
    requires exists (k: int64) { k == x };
    ensures exists (z: int64) { z == x } by {
        obtain (k: int64) { k == x }
        have k == x by assumption();
        witness { z: k };
        assumption();
    }
}

theorem obtained_uint64(x: uint64) {
    requires exists (k: uint64) { k == x };
    ensures exists (z: uint64) { z == x } by {
        obtain (k: uint64) { k == x }
        have k == x by assumption();
        witness { z: k };
        assumption();
    }
}

theorem obtained_integer(x: Integer) {
    requires exists (k: Integer) { k == x };
    ensures exists (z: Integer) { z == x } by {
        obtain (k: Integer) { k == x }
        have k == x by assumption();
        witness { z: k };
        assumption();
    }
}

theorem obtained_algebraic(x: Nat) {
    requires exists (k: Nat) { k == x };
    ensures exists (z: Nat) { z == x } by {
        obtain (k: Nat) { k == x }
        have k == x by assumption();
        witness { z: k };
        assumption();
    }
}

theorem obtained_pointer(x: int32*) {
    requires exists (k: int32*) { k == x };
    ensures exists (z: int32*) { z == x } by {
        obtain (k: int32*) { k == x }
        have k == x by assumption();
        witness { z: k };
        assumption();
    }
}
```

```expect
pass
```
