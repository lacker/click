# pure-function unfold opens exactly one definition layer

`unfold(function(args))` is a deterministic simple step. It exposes the
selected call's defining equation at the current proof state; it does not
recursively expand the call tree.

```click
function clamp_nonpositive(n: int32) -> int32 {
    if n <= 0 { 0 } else { n }
}

theorem clamp_nonpositive_is_zero(n: int32) {
    requires n <= 0;
    ensures clamp_nonpositive(n) == 0 by {
        unfold(clamp_nonpositive(n));
        normalize();
    }
}
```

```expect
pass
```
