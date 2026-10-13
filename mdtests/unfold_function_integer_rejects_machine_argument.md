# An introduced Integer remains specification-side in a function argument

```click
function machine(x: int32) -> int32 { x }
theorem rejects_integer_machine_argument() {
    ensures forall (d: Integer) { d == d } by {
        intro();
        unfold(machine(d));
        normalize();
    }
}
```

```expect
fail: could not lower defining equation for `machine`
```
