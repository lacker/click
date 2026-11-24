# recursive pure proofs do not start induction implicitly

One symbolic equation is exposed, but `solve` does not invent an induction
hypothesis or unfold recursively to an arbitrary depth.

```click
function explicit_countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { explicit_countdown(n - 1) }
}

theorem missing_induction(n: int32) {
    requires n >= 0;
    ensures explicit_countdown(n) == 0 by {
        if n <= 0 {
            close();
        } else {
            close();
        }
    }
}
```

```expect
fail: `solve` failed
```
