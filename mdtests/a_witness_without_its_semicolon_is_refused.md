# A `witness` without its semicolon is refused

`witness { ... }` is a statement and ends with `;`, like every other proof
step.

```c filename=a_witness_without_its_semicolon_is_refused.c
int32 zero(int32 n) { return 0; }
```

```click
verifying "a_witness_without_its_semicolon_is_refused.c";

int32 zero(int32 n) {
    requires 0 < n;
    ensures (0..n).any(|k| { k == result }) by {
        execute();
        witness { k: 0 }
        simp();
    }
}
```

```expect
fail: expected `;` after `witness { ... }`
```
