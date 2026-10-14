# an unsigned parameter ranks a recursion by its own descent

Euclid's algorithm lowers `b` to `a % b`, which is not a constant decrement,
and `b` is unsigned. `decreases b` names that parameter, and because only an
`int32` parameter has the body analysis `decreases n` uses, an unsigned one is
an expression measure: each self-call owes `a % b < b`, stated with the
prelude's remainder law. An unsigned value needs no nonnegativity member.

```c filename=c_decreases_unsigned_parameter_recursion.c
unsigned int gcd(unsigned int a, unsigned int b) {
    if (b == 0) {
        return a;
    }
    return gcd(b, a % b);
}
```

```click
verifying "c_decreases_unsigned_parameter_recursion.c";

uint32 gcd(uint32 a, uint32 b) {
    decreases b;
    ensures result >= 0u32;
} by {
    branch then {
        step();
        simp();
    } else {}
    have a % b < b by {
        apply(uint32_remainder_less_than_divisor(a, b)) using {
            b != 0u32;
        }
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
