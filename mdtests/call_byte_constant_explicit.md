# Explicit byte read through a modular contract

```c filename=byte.c
uint8 first(uint8 *p) { return p[0]; }
uint8 local() { uint8 bytes[1] = {3}; return first(bytes); }
```

```click
verifying "byte.c";
uint8 first(uint8 *p) { views p[0..1]; ensures result == p[0]; }
uint8 local() { ensures result == 3 by {
    step();
    step();
    step();
    step();
    have result == 3 by {
        close();
    }
    close();
} }
```

```expect
pass
```
