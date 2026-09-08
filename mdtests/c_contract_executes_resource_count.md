# The final implication check must not re-prove an already checked postcondition

```click
abstract resource Permit(x: int32);
contract void Raw(int32 x) { owns Permit(x); }
contract void Target(int32 x) {
    requires count(Permit(x)) == 1;
    owns Permit(x);
    ensures count(Permit(x)) == 1;
}
theorem lift(callback: void (*)(int32)) executes callback(int32 value) {
    requires Raw(callback);
    ensures Target(callback) by { step(Raw); simp(); }
}
```

```expect
pass
```
