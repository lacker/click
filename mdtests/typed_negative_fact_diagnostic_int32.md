# A checked int32 fact retains its constant's signedness

```c filename=typed_negative_fact_diagnostic_int32.c
int32 value(void) { return -56; }
int32 caller(void) { return value(); }
```

```click
verifying "typed_negative_fact_diagnostic_int32.c";
int32 value() { ensures result == -56 by auto; }
int32 caller() { ensures result == 200 by auto; }
```

```expect
fail: pure facts: [result == -56]
```
