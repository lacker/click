# Function declarations cannot change a parameter's pointee qualification

```c filename=const_parameter_signature.c
int32 read(const int32 *p);
int32 read(int32 *p) { return p[0]; }
```

```click
verifying "const_parameter_signature.c";
```

```expect
fail:conflicting declarations
```
