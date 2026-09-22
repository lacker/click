# Explicit signed int spelling

`signed int` uses the existing signed 32-bit model in declarations, typedefs,
pointers, casts, and `sizeof`.

```c filename=signed_int.c
typedef signed int header_integer;
header_integer identity(signed int value) { return value; }
signed int negative(void) { return -1; }
int width(void) { return sizeof(signed int); }
signed int cast(int value) { return (signed int)value; }
signed int read(signed int *p) { return *p; }
signed int increment(signed int value) { return value + 1; }
```

```click
verifying "signed_int.c";
signed int identity(int value) { ensures result == value by auto; }
signed int negative() { ensures result == -1 by auto; }
int width() { ensures result == 4 by auto; }
int cast(signed int value) { ensures result == value by auto; }
signed int read(signed int *p) {
    views p[0..1];
    ensures result == p[0] by auto;
}
signed int increment(signed int value) {
    requires value < 2147483647;
    ensures result == value + 1 by auto;
}
```

```expect
pass
```
