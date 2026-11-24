# Callback refinement retains its checked population-count postcondition

The scalar logical controls retain their original signatures separately. This
population companion exercises the same final implication boundary with an
explicit pointer anchor and arbitrary imported total constrained by the target.

```click
authorized resource Permit(pool: int32*) {}
contract void Raw(int32* pool) {
    owns authority(Permit(pool));
    owns Permit(pool);
}
contract void Target(int32* pool) {
    requires count(Permit(pool)) == 1;
    owns authority(Permit(pool));
    owns Permit(pool);
    ensures count(Permit(pool)) == 1;
}
theorem lift(callback: void (*)(int32*)) executes callback(int32* pool) {
    requires Raw(callback);
    ensures Target(callback) by { step(Raw); close(); }
}
```

```expect
pass
```
