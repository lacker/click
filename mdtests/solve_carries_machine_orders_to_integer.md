# The implicit closer carries machine order facts to `Integer`

On a stated `Integer` fact, the implicit closer reads the machine order facts connected
to it through their bridge theorems (`integer::int32_less_equal_to_integer`,
...), then refutes the fact's negation. The
expansion keeps only the bridges the certificate cites.

```click
theorem bridged_uint64(i: uint64, n: uint64) {
    requires i < n;
    requires n <= 1000u64;
    ensures to_integer(i) <= 999 by {
        have to_integer(i) <= 999;
        close();
    }
}

theorem bridged_int32(total: int32, b: int32) {
    requires 0 <= b;
    requires b <= 255;
    requires to_integer(total) <= 255000;
    ensures to_integer(total) + to_integer(b) <= 2147483647 by {
        have to_integer(total) + to_integer(b) <= 2147483647;
        close();
    }
}
```

```expect
pass
```
