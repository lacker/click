# `arithmetic using` crosses a machine successor

`a < b + 1` is `a <= b`: the machine successor wraps only when `b` is the
signed maximum, and the wrapped successor is then the signed minimum, so the
strict premise is unsatisfiable. The bound therefore needs no definedness
premise, and `arithmetic() using` plans it from the one listed premise.

The second theorem spells the planned step directly; it is exactly what
`click expand` prints for the first one.

```click
theorem strict_succ(a: int32, b: int32) {
    requires b < 1000;
    requires a < b + 1;
    ensures a <= b by {
        arithmetic() using {
            a < b + 1;
        }
    }
}

theorem strict_succ_explicit(a: int32, b: int32) {
    requires a < b + 1;
    ensures a <= b by {
        arithmetic_certificate signed_int32 {
            strict_successor 0: a < b + 1 => a <= b;
            conclusion 0;
        }
    }
}
```

```expect
pass
```
