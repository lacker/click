# A function qualifier cannot select between shadowed static declarations

```c filename=ambiguous.c
void f(int flag) {
    static int cell;
    if (flag) { static int cell; cell = 1; }
    cell = 2;
}
```

```click
verifying "ambiguous.c" as source;
void f(int flag) { owns &source::f::cell[0..1]; }
```

```expect
fail: ambiguous function-local static `source::f::cell`
```
