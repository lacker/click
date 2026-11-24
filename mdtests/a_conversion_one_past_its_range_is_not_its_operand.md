# A conversion one past its range is not its operand

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=a_conversion_one_past_its_range_is_not_its_operand.c
int next_byte(int x) { unsigned char y = x + 1; return y; }
```

```click
verifying "a_conversion_one_past_its_range_is_not_its_operand.c";
int32 next_byte(int32 x) {
    requires 0 <= x;
    requires x < 256;
    ensures result == x + 1;
} by {
    step();
    step();
    step();
    have result == (x + 1) by {
        close() using { at(function.entry, x < 256); at(function.entry, 0 <= x); };
    }
    close();
}
```

```expect
fail: `close() using`
```
