# A checked uint32 fact retains its constant's signedness

```c filename=typed_negative_fact_diagnostic_uint32.c
uint32 value(void) { return 4294967240u; }
uint32 caller(void) { return value(); }
```

```click
verifying "typed_negative_fact_diagnostic_uint32.c";
uint32 value() { ensures result == 4294967240u32 by auto; }
uint32 caller() { ensures result == 200u32 by auto; }
```

```expect
fail: uint32 =(value A, 4294967240)
```
