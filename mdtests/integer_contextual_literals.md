# contextual mathematical Integer literals

```click
theorem integer_contextual_literals(x: Integer) {
    let z: Integer = -1;
    let int64_boundary: Integer = 2147483648;
    let negative_int64_boundary: Integer = -2147483649;
    let wide_unsigned: Integer = 4294967296;
    let u64_boundary: Integer = 18446744073709551615;
    ensures (1 + 2) + z == z + (1 + 2) by {
        simp();
    }
    ensures int64_boundary == 2147483648 by { simp(); }
    ensures negative_int64_boundary == -2147483649 by { simp(); }
    ensures wide_unsigned == 4294967296 by { simp(); }
    ensures u64_boundary == 18446744073709551615 by { simp(); }
}
```

```expect
pass
```
