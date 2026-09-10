# Zero-fill floating-point fields in local struct initializers

Omitted fields in a local aggregate initializer are zero-initialized for both
single- and double-precision floating-point fields.

```c filename=local_struct_float_double_zero_initializer.c
struct sample {
    int32 present;
    float single;
    double wide;
};

int32 local_struct_float_double_zero_initializer() {
    struct sample sample = {7};
    return sample.present + (sample.single == 0.0f) + (sample.wide == 0.0);
}
```

```click
verifying "local_struct_float_double_zero_initializer.c";

int32 local_struct_float_double_zero_initializer() {
    ensures result == 9 by auto;
}
```

```expect
pass
```
