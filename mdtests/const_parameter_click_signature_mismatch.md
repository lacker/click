# Click signatures cannot change a parameter's pointee qualification

```c filename=const_parameter_click_signature.c
int32 read(int32 *p) { return p[0]; }
```

```click
verifying "const_parameter_click_signature.c";
int32 read(const int32 *p) { ensures result == 0; }
```

```expect
fail:signature mismatch
```
