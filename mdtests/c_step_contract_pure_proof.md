# Selecting a contract does not give a pure theorem an execution frontier

```click
contract int32 Identity(int32 x) { ensures result == x; }
theorem reflexive(x: int32) {
    ensures x == x by { step(Identity); }
}
```

```expect
fail: is not available in the pure proof
```
