# Return-valued proofs preserve wide scalar results

```click
contract uint64 Raw(uint64 x) { ensures result == x; }
contract uint64 Target(uint64 x) { ensures result == x; }
theorem lift(callback: uint64 (*)(uint64)) executes callback(uint64 value) {
    requires Raw(callback);
    ensures Target(callback) by { step(Raw); have result == value by { assumption(); } simp(); }
}
```

```expect
pass
```
