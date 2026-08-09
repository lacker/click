# restricted simp pointer alias loadability

An explicit equality rewrite may mention an element through a pointer alias.
The surrounding array ownership makes the expression loadable; the restricted
simplifier must use only its listed equalities to prove the value claim, and
its expanded certificate must replay without requiring a redundant
element-loadability premise.

```c filename=restricted_simp_pointer_alias_loadability.c
int32 alias_value(
    int32 original[],
    int32 alias[],
    int32 length,
    int32 value
) {
    return value;
}
```

```click
verifying "restricted_simp_pointer_alias_loadability.c";

resource valued_array(data: int32*, length: int32, value: int32) {
    owns data[0..length];
    fact 1 <= length;
    fact data[0] == value;
}

int32 alias_value(
    int32 original[],
    int32 alias[],
    int32 length,
    int32 value
) {
    requires alias == original;
    owns valued_array(original, length, value);
    ensures alias[0] == value;
} by {
    unfold(valued_array(original, length, value));
    step();
    have alias[0] == value by {
        simp() using {
            original[0] == value;
            alias == original;
        }
    }
    fold(valued_array(original, length, value));
    simp();
}
```

```expect
pass
```
