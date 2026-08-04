# pure induction keeps other theorem parameters fixed

The induction hypothesis varies only the named measure. Other theorem
parameters keep their current symbolic values.

```click
function add_after_countdown(n: int32, extra: int32) -> int32
    decreases n
{
    if n <= 0 { extra } else { add_after_countdown(n - 1, extra) }
}

theorem add_after_countdown_returns_extra(n: int32, extra: int32) {
    requires n >= 0;
    ensures add_after_countdown(n, extra) == extra by {
        induct(n) as ih;
        if n <= 0 {
            simp();
        } else {
            apply(ih(n - 1));
            simp();
        }
    }
}
```

```expect
pass
```
